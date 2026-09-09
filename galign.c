#include <assert.h>
#include <string.h>
#include "mgpriv.h"
#include "kalloc.h"
#include "kthread.h"
#include "miniwfa.h"

/******************
 * Generate cigar *
 ******************/

static void append_cigar1(void *km, mg64_v *c, int32_t op, int32_t len)
{
	if (c->n > 0 && (c->a[c->n - 1]&0xf) == op) {
		c->a[c->n - 1] += (uint64_t)len<<4;
	} else {
		if (c->n == c->m) {
			c->m += (c->m>>1) + 16;
			KREALLOC(km, c->a, c->m);
		}
		c->a[c->n++] = (uint64_t)len<<4 | op;
	}
}

static void append_cigar(void *km, mg64_v *c, int32_t n_cigar, const uint32_t *cigar)
{
	int32_t k;
	if (n_cigar == 0) return;
	append_cigar1(km, c, cigar[0]&0xf, cigar[0]>>4);
	if (c->n + n_cigar - 1 > c->m) {
		c->m = c->n + n_cigar - 1;
		kroundup32(c->m);
		KREALLOC(km, c->a, c->m);
	}
	for (k = 0; k < n_cigar - 1; ++k)
		c->a[c->n + k] = cigar[1 + k];
	c->n += n_cigar - 1;
}

// find the llchain that contains anchor _ai_, searching from _l0_ as the serial loop does
static inline int32_t cigar_find_lc(const mg_gchains_t *gt, int32_t l_end, int32_t l0, int32_t ai)
{
	int32_t l;
	for (l = l0; l < l_end; ++l) {
		const mg_llchain_t *r = &gt->lc[l];
		if (ai >= r->off && ai < r->off + r->cnt)
			break;
	}
	assert(l < l_end);
	return l;
}

// length of the target sequence between the anchor at qx on lc[l0] and the anchor at px on lc[l]
static inline int32_t cigar_tlen(const gfa_t *g, const gfa_edseq_t *es, const mg_gchains_t *gt, int32_t l0, int32_t l, int32_t qx, int32_t px)
{
	int32_t k, l_seq;
	if (l == l0) { // on the same vertex
		l_seq = px - qx;
	} else {
		l_seq = g->seg[gt->lc[l0].v>>1].len - qx - 1;
		for (k = l0 + 1; k < l; ++k)
			l_seq += es[gt->lc[k].v].len;
		l_seq += px + 1;
	}
	return l_seq;
}

// concatenate the vertex sequences between the two anchors into *seq, growing it as needed; returns the length
static int32_t cigar_tseq(void *km, const gfa_t *g, const gfa_edseq_t *es, const mg_gchains_t *gt, int32_t l0, int32_t l, int32_t qx, int32_t px, char **seq, int32_t *m_seq)
{
	int32_t k, l_seq;
	l_seq = cigar_tlen(g, es, gt, l0, l, qx, px);
	if (l_seq + 1 > *m_seq) {
		*m_seq = l_seq + 1;
		kroundup32(*m_seq);
		KREALLOC(km, *seq, *m_seq);
	}
	if (l == l0) { // on the same vertex
		memcpy(*seq, &es[gt->lc[l0].v].seq[qx + 1], l_seq);
	} else {
		uint32_t v = gt->lc[l0].v;
		l_seq = g->seg[v>>1].len - qx - 1;
		memcpy(*seq, &es[v].seq[qx + 1], l_seq);
		for (k = l0 + 1; k < l; ++k) {
			v = gt->lc[k].v;
			memcpy(&(*seq)[l_seq], es[v].seq, es[v].len);
			l_seq += es[v].len;
		}
		memcpy(&(*seq)[l_seq], es[gt->lc[l].v].seq, px + 1);
		l_seq += px + 1;
	}
	return l_seq;
}

// save the CIGAR to gc and derive its statistics, exactly as the serial code does
static void cigar_save(mg_gchains_t *gt, mg_gchain_t *gc, int32_t off_a0, const mg64_v *cigar)
{
	int32_t j, l;
	gc->p = (mg_cigar_t*)kcalloc(gt->km, 1, cigar->n * 8 + sizeof(mg_cigar_t));
	gc->p->ss = (int32_t)gt->a[off_a0].x + 1 - (int32_t)(gt->a[off_a0].y>>32&0xff);
	gc->p->ee = (int32_t)gt->a[off_a0 + gc->n_anchor - 1].x + 1;
	gc->p->n_cigar = cigar->n;
	memcpy(gc->p->cigar, cigar->a, cigar->n * 8);
	for (j = 0, l = 0; j < gc->p->n_cigar; ++j) {
		int32_t op = gc->p->cigar[j]&0xf, len = gc->p->cigar[j]>>4;
		if (op == 7) gc->p->mlen += len, gc->p->blen += len;
		else gc->p->blen += len;
		if (op != 1) gc->p->aplen += len;
		if (op != 2) l += len;
	}
	memset(&gc->ds, 0, sizeof(gc->ds));
	assert(l == gc->qe - gc->qs && gc->p->aplen == gc->pe - gc->ps);
}

/*****************************************************************************
 * Aligning the anchor gaps of one query in parallel
 *
 * mg_gchain_cigar() walks the anchors of every gchain in order and appends one
 * CIGAR piece per anchor gap. Nearly all the time is in mwf_wfa_auto(), which
 * is a pure function of the target sequence between the two anchors and the
 * query between them: it allocates only from the arena it is handed and its
 * only output is the CIGAR. Everything else - finding the containing llchain,
 * measuring the target, and the three fixed-op shortcuts - is cheap, and only
 * the appending is order-dependent.
 *
 * So split the loop in three. Phase A (serial) walks the anchors exactly as
 * the core loop does and lists only the gaps that reach the alignment branch,
 * recording the two llchains and the two lengths. Phase B aligns them with
 * kt_for(), each thread rebuilding its own target sequence in a private buffer
 * and aligning in a private malloc-backed arena, and keeps a copy of the
 * CIGAR. Phase C is the original loop, except that the alignment branch
 * replays the recorded CIGAR through the same append_cigar() call instead of
 * aligning, and the target sequence is only measured, not built. The pieces
 * are appended in the same order by the same code, so the stored CIGAR is
 * byte-identical whatever the thread count. With n_threads <= 1 there is no
 * Phase A or B and the core loop is the original code.
 *****************************************************************************/

#define MG_CIGAR_PAR_MIN_TASK 16 // don't start threads for fewer alignments than this

typedef struct { // one anchor gap gt->a[off_a0+j0] -> gt->a[off_a0+j] that needs an alignment
	int32_t gc_i;         // the gchain this gap belongs to; the tasks are in gchain and anchor order
	int32_t off_a0;       // gt->lc[gc->off].off
	int32_t j0, j;        // anchor indices within the gchain
	int32_t l0, l;        // the llchains containing the two anchors
	int32_t l_seq, qlen;  // target and query length of the gap
	int32_t n_cigar;      // Phase B output
	uint32_t *cigar;      // Phase B output, allocated from the worker's arena
} cigar_task_t;

typedef struct {
	void *km_out;   // holds the CIGAR copies until Phase C; lives to the end
	void *km_wfa;   // mwf_wfa_auto() scratch; recycled after a big alignment, as km2 is in the serial code
	char *seq;      // target sequence buffer, malloc-backed
	int32_t m_seq;
} cigar_worker_t;

typedef struct {
	const gfa_t *g;
	const gfa_edseq_t *es;
	const mg_gchains_t *gt;
	const char *qseq, *qname;
	cigar_task_t *task;
	cigar_worker_t *w;   // one per thread
} cigar_par_t;

static void cigar_worker(void *data, long k, int tid) // kt_for() callback: one alignment per call
{
	cigar_par_t *cp = (cigar_par_t*)data;
	cigar_worker_t *w = &cp->w[tid];
	cigar_task_t *t = &cp->task[k];
	const mg128_t *q = &cp->gt->a[t->off_a0 + t->j0];
	const char *qs = &cp->qseq[(int32_t)q->y + 1];
	mwf_opt_t opt;
	mwf_rst_t rst;
	int32_t l_seq;
	// NB: km_init2(0,...) is malloc-backed, so the caller's arena - which is not thread-safe - is untouched.
	// The core size is the 1MB of lchain.c rather than the 8MB default of km_init(): there are two of these
	// arenas per worker and they are re-created for every query, so the default floor would reserve
	// n_threads*16MB per query to hold a CIGAR list that is a few KB.
	if (w->km_out == 0) w->km_out = km_init2(0, 0x10000);
	if (w->km_wfa == 0) w->km_wfa = km_init2(0, 0x10000);
	l_seq = cigar_tseq(0, cp->g, cp->es, cp->gt, t->l0, t->l, (int32_t)q->x, (int32_t)cp->gt->a[t->off_a0 + t->j].x, &w->seq, &w->m_seq);
	assert(l_seq == t->l_seq);
	mwf_opt_init(&opt);
	opt.flag |= MWF_F_CIGAR;
	mwf_wfa_auto(w->km_wfa, &opt, l_seq, w->seq, t->qlen, qs, &rst);
	t->n_cigar = rst.n_cigar;
	if (rst.n_cigar > 0) { // keep the CIGAR for Phase C
		KMALLOC(w->km_out, t->cigar, rst.n_cigar);
		memcpy(t->cigar, rst.cigar, rst.n_cigar * 4);
	}
	kfree(w->km_wfa, rst.cigar);
	if ((mg_dbg_flag&MG_DBG_MINIWFA) && l_seq > 5000 && t->qlen > 5000 && rst.s >= 10000)
		fprintf(stderr, "WL\t%s\t%d\t%d\t%d\t%d\t%d\n", cp->qname, t->gc_i, (int32_t)q->y + 1, t->qlen, l_seq, rst.s);
	if ((mg_dbg_flag&MG_DBG_MWF_SEQ) && l_seq > 5000 && t->qlen > 5000 && rst.s >= 10000) {
		char *str;
		int32_t n;
		str = Kmalloc(w->km_wfa, char, t->qlen + l_seq + strlen(cp->qname) + 100);
		n = sprintf(str, "WL\t%s\t%d\t%d\t%d\nWT\t%.*s\nWQ\t%.*s\n", cp->qname, t->gc_i, (int32_t)q->y + 1, rst.s, l_seq, w->seq, t->qlen, qs);
		fwrite(str, 1, n, stderr);
		kfree(w->km_wfa, str);
	}
	if (rst.s >= 10000 && l_seq > 5000 && t->qlen > 5000) { // the memory hygiene heuristic of the serial code, per worker
		km_destroy(w->km_wfa);
		w->km_wfa = km_init2(0, 0x10000);
	}
}

// With n_threads > 1 the gaps that need an alignment are aligned in parallel; the CIGAR does not depend on n_threads.
void mg_gchain_cigar(void *km, const gfa_t *g, const gfa_edseq_t *es, const char *qseq, mg_gchains_t *gt, const char *qname, int n_threads) // qname for debugging only
{
	int32_t i, l_seq = 0, m_seq = 0;
	int32_t par, n_task = 0, m_task = 0, ti = 0, nt = 0;
	char *seq = 0;
	void *km2 = 0;
	cigar_task_t *task = 0;
	cigar_worker_t *w = 0;
	mg64_v cigar = {0,0,0};

	par = (n_threads > 1);
	if (par) {
		// Phase A: walk the anchors exactly as the core loop below does and list the gaps that need an alignment
		for (i = 0; i < gt->n_gc; ++i) {
			const mg_gchain_t *gc = &gt->gc[i];
			int32_t l0 = gc->off;
			int32_t off_a0 = gt->lc[l0].off;
			int32_t j, j0 = 0, l;
			for (j = 1; j < gc->n_anchor; ++j) {
				const mg128_t *q, *p = &gt->a[off_a0 + j];
				int32_t qlen;
				if ((p->y & MG_SEED_IGNORE) && j != gc->n_anchor - 1) continue;
				q = &gt->a[off_a0 + j0];
				l = cigar_find_lc(gt, gc->off + gc->cnt, l0, off_a0 + j);
				l_seq = cigar_tlen(g, es, gt, l0, l, (int32_t)q->x, (int32_t)p->x);
				qlen = (int32_t)p->y - (int32_t)q->y;
				if (l_seq > 0 && qlen > 0 && !(l_seq == qlen && qlen <= (q->y>>32&0xff))) { // the "else" branch of the core loop
					cigar_task_t *t;
					if (n_task == m_task) KEXPAND(km, task, m_task);
					t = &task[n_task++];
					t->gc_i = i, t->off_a0 = off_a0, t->j0 = j0, t->j = j, t->l0 = l0, t->l = l;
					t->l_seq = l_seq, t->qlen = qlen;
					t->n_cigar = 0, t->cigar = 0;
				}
				j0 = j, l0 = l;
			}
		}
		// Phase B: align the listed gaps, each thread in its own arena
		if (n_task > 0) {
			cigar_par_t cp;
			nt = n_task >= MG_CIGAR_PAR_MIN_TASK? n_threads : 1;
			if (nt > n_task) nt = n_task;
			KCALLOC(km, w, nt);
			memset(&cp, 0, sizeof(cp));
			cp.g = g, cp.es = es, cp.gt = gt, cp.qseq = qseq, cp.qname = qname, cp.task = task, cp.w = w;
			if (nt > 1) kt_for(nt, cigar_worker, &cp, n_task);
			else for (i = 0; i < n_task; ++i) cigar_worker(&cp, i, 0);
		}
		if (mg_dbg_flag & MG_DBG_LC_PROF) fprintf(stderr, "CP\t%s\tn_aln=%d\tnt=%d\n", qname, n_task, nt);
	} else km2 = km_init2(km, 0);

	// core loop (Phase C when par: the recorded CIGARs are replayed instead of aligned here)
	for (i = 0; i < gt->n_gc; ++i) {
		mg_gchain_t *gc = &gt->gc[i];
		int32_t l0 = gc->off;
		int32_t off_a0 = gt->lc[l0].off;
		int32_t j, j0 = 0, k, l;
		cigar.n = 0;
		append_cigar1(km, &cigar, 7, gt->a[off_a0].y>>32&0xff);
		for (j = 1; j < gc->n_anchor; ++j) {
			const mg128_t *q, *p = &gt->a[off_a0 + j];
			if ((p->y & MG_SEED_IGNORE) && j != gc->n_anchor - 1) continue;
			q = &gt->a[off_a0 + j0];
			l = cigar_find_lc(gt, gc->off + gc->cnt, l0, off_a0 + j); // find the lchain that contains the anchor
			assert((int32_t)q->x < g->seg[gt->lc[l0].v>>1].len);
			// get the target sequence; under par only its length is needed, the workers build their own
			l_seq = par? cigar_tlen(g, es, gt, l0, l, (int32_t)q->x, (int32_t)p->x)
					   : cigar_tseq(km, g, es, gt, l0, l, (int32_t)q->x, (int32_t)p->x, &seq, &m_seq);
			{
				int32_t qlen = (int32_t)p->y - (int32_t)q->y;
				const char *qs = &qseq[(int32_t)q->y + 1];
				assert(l_seq > 0 || qlen > 0);
				if (l_seq == 0) append_cigar1(km, &cigar, 1, qlen);
				else if (qlen == 0) append_cigar1(km, &cigar, 2, l_seq);
				else if (l_seq == qlen && qlen <= (q->y>>32&0xff)) append_cigar1(km, &cigar, 7, qlen);
				else if (par) { // replay the CIGAR computed in Phase B; the tasks are in walk order
					const cigar_task_t *t = &task[ti++];
					assert(ti <= n_task && t->gc_i == i && t->j0 == j0 && t->j == j);
					append_cigar(km, &cigar, t->n_cigar, t->cigar);
				} else {
					mwf_opt_t opt;
					mwf_rst_t rst;
					mwf_opt_init(&opt);
					opt.flag |= MWF_F_CIGAR;
					mwf_wfa_auto(km2, &opt, l_seq, seq, qlen, qs, &rst);
					append_cigar(km, &cigar, rst.n_cigar, rst.cigar);
					kfree(km2, rst.cigar);
					if ((mg_dbg_flag&MG_DBG_MINIWFA) && l_seq > 5000 && qlen > 5000 && rst.s >= 10000)
						fprintf(stderr, "WL\t%s\t%d\t%d\t%d\t%d\t%d\n", qname, i, (int32_t)q->y + 1, (int32_t)p->y - (int32_t)q->y, l_seq, rst.s);
					if (rst.s >= 10000 && l_seq > 5000 && qlen > 5000) {
						km_destroy(km2);
						km2 = km_init2(km, 0);
					}
					if ((mg_dbg_flag&MG_DBG_MWF_SEQ) && l_seq > 5000 && qlen > 5000 && rst.s >= 10000) {
						char *str;
						str = Kmalloc(km, char, qlen + l_seq + strlen(qname) + 100);
						k = sprintf(str, "WL\t%s\t%d\t%d\t%d\nWT\t%.*s\nWQ\t%.*s\n", qname, i, (int32_t)q->y + 1, rst.s, l_seq, seq, qlen, qs);
						fwrite(str, 1, k, stderr);
						kfree(km, str);
					}
				}
			}
			j0 = j, l0 = l;
		}
		cigar_save(gt, gc, off_a0, &cigar); // save the CIGAR to gt->gc[i]
	}
	assert(ti == n_task);

	if (km2) km_destroy(km2);
	for (i = 0; i < nt; ++i) { // the recorded CIGARs live in the worker arenas
		if (w[i].km_out) km_destroy(w[i].km_out);
		if (w[i].km_wfa) km_destroy(w[i].km_wfa);
		free(w[i].seq);
	}
	kfree(km, w);
	kfree(km, task);
	kfree(km, seq);
	kfree(km, cigar.a);
}

/***********************
 * Generate the ds tag *
 ***********************/

#define mg_get_nucl(s, i) (seq_nt4_table[(uint8_t)(s)[(i)]]) // get the base in the "nt4" encoding

static void write_indel(void *km, kstring_t *str, int64_t len, const char *seq, int64_t ll, int64_t lr) // write an indel to ds
{
	int64_t i;
	if (ll + lr >= len) {
		mg_sprintf_km(km, str, "[");
		for (i = 0; i < len; ++i)
			mg_sprintf_km(km, str, "%c", "acgtn"[mg_get_nucl(seq, i)]);
		mg_sprintf_km(km, str, "]");
	} else {
		int64_t k = 0;
		if (ll > 0) {
			mg_sprintf_km(km, str, "[");
			for (i = 0; i < ll; ++i)
				mg_sprintf_km(km, str, "%c", "acgtn"[mg_get_nucl(seq, k+i)]);
			mg_sprintf_km(km, str, "]");
			k += ll;
		}
		for (i = 0; i < len - lr - ll; ++i)
			mg_sprintf_km(km, str, "%c", "acgtn"[mg_get_nucl(seq, k+i)]);
		k += len - lr - ll;
		if (lr > 0) {
			mg_sprintf_km(km, str, "[");
			for (i = 0; i < lr; ++i)
				mg_sprintf_km(km, str, "%c", "acgtn"[mg_get_nucl(seq, k+i)]);
			mg_sprintf_km(km, str, "]");
		}
	}
}

void mg_gchain_gen_ds(void *km, const gfa_t *g, const gfa_edseq_t *es, const char *qseq, mg_gchains_t *gt)
{
	int32_t i, m_off = 0, n_off = 0, *off = 0;
	void *km2;
	kstring_t str = {0,0,0}, seq = {0,0,0};
	km2 = km_init2(km, 0);
	for (i = 0; i < gt->n_gc; ++i) {
		mg_gchain_t *gc = &gt->gc[i];
		int32_t j;
		int64_t x, y, ds_len;
		str.l = seq.l = n_off = 0;
		if (gc->p->aplen > seq.m) {
			seq.s = Krealloc(km2, char, seq.s, gc->p->aplen);
			seq.m = gc->p->aplen;
		}
		for (j = 0, seq.l = 0; j < gc->cnt; ++j) { // extract the aligned sequence in the graph
			int32_t k = gc->off + j;
			uint32_t v = gt->lc[k].v;
			int32_t slen = es[v].len;
			int32_t st = j > 0? 0 : gc->p->ss;
			int32_t en = j < gc->cnt - 1? slen : gc->p->ee;
			assert(seq.l + (en - st) <= gc->p->aplen);
			memcpy(&seq.s[seq.l], &es[v].seq[st], en - st);
			seq.l += en - st;
		}
		assert(seq.l == gc->p->aplen);
		for (j = 0, x = 0, y = gc->qs, ds_len = 0, n_off = 0; j < gc->p->n_cigar; ++j) { // estimate the approximate length of ds
			int64_t op = gc->p->cigar[j]&0xf, len = gc->p->cigar[j]>>4, z;
			if (op == 0 || op == 7 || op == 8) { // alignment match
				int32_t l = 0;
				++n_off;
				for (z = 0; z < len; ++z) {
					if (mg_get_nucl(seq.s, x+z) != mg_get_nucl(qseq, y+z))
						ds_len += 3, ds_len += 6, n_off += 2, l = 0;
					else ++l;
				}
				ds_len += 6;
				x += len, y += len;
			} else if (op == 1) { // insertion
				ds_len += len + 1, ++n_off, y += len;
			} else if (op == 2) { // deletion
				ds_len += len + 1, ++n_off, x += len;
			}
		}
		if (n_off > m_off) {
			m_off = n_off + (n_off>>1) + 16;
			off = Krealloc(km2, int32_t, off, m_off);
		}
		mg_str_reserve(km2, &str, ds_len);
		for (j = 0, x = 0, y = gc->qs, n_off = 0; j < gc->p->n_cigar; ++j) { // write ds
			int64_t op = gc->p->cigar[j]&0xf, len = gc->p->cigar[j]>>4;
			assert(n_off < m_off);
			if (op == 0 || op == 7 || op == 8) { // alignment match
				int64_t z;
				int32_t l = 0;
				for (z = 0; z < len; ++z) {
					uint8_t cx = mg_get_nucl(seq.s, x+z);
					uint8_t cy = mg_get_nucl(qseq, y+z);
					if (cx != cy) {
						if (l > 0) {
							off[n_off++] = str.l;
							mg_sprintf_km(km2, &str, ":%d", l);
						}
						off[n_off++] = str.l;
						mg_sprintf_km(km2, &str, "*%c%c", "acgtn"[cx], "acgtn"[cy]);
						l = 0;
					} else ++l;
				}
				if (l > 0) {
					off[n_off++] = str.l;
					mg_sprintf_km(km2, &str, ":%d", l);
				}
				x += len, y += len;
			} else if (op == 1) { // insertion
				int64_t z, ll, lr;
				for (z = 1; z <= len; ++z)
					if (y - z < gc->qs || qseq[y + len - z] != qseq[y - z])
						break;
				lr = z - 1;
				for (z = 0; z < len; ++z)
					if (y + len + z >= gc->qe || qseq[y + len + z] != qseq[y + z])
						break;
				ll = z;
				off[n_off++] = str.l;
				mg_sprintf_km(km2, &str, "+");
				write_indel(km2, &str, len, &qseq[y], ll, lr);
				y += len;
			} else if (op == 2) { // deletion
				int64_t z, ll, lr;
				for (z = 1; z <= len; ++z)
					if (x - z < 0 || seq.s[x + len - z] != seq.s[x - z])
						break;
				lr = z - 1;
				for (z = 0; z < len; ++z)
					if (x + len + z >= gc->p->aplen || seq.s[x + z] != seq.s[x + len + z])
						break;
				ll = z;
				off[n_off++] = str.l;
				mg_sprintf_km(km2, &str, "-");
				write_indel(km2, &str, len, &seq.s[x], ll, lr);
				x += len;
			}
		}
		gc->ds.len = str.l;
		gc->ds.ds = Kcalloc(gt->km, char, str.l + 1);
		memcpy(gc->ds.ds, str.s, str.l);
		gc->ds.n_off = n_off;
		gc->ds.off = Kcalloc(gt->km, int32_t, n_off);
		memcpy(gc->ds.off, off, n_off * sizeof(int32_t));
	}
	km_destroy(km2); // this frees both str.s and seq.s
}
