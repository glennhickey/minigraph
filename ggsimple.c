#include <assert.h>
#include <ctype.h>
#include <string.h>
#include "mgpriv.h"
#include "gfa-priv.h"
#include "kalloc.h"
#include "bseq.h"
#include "algo.h"
#include "sys.h"
#include "ggen.h"
#include "kvec-km.h"

int32_t mg_gc_index(void *km, int min_mapq, int min_map_len, int min_depth_len, const gfa_t *g, int32_t n_seq, mg_gchains_t *const* gcs,
					double *a_dens, int32_t **soff_, int32_t **qoff_, mg_intv_t **sintv_, mg_intv_t **qintv_)
{
	int32_t t, i, j, max_acnt, *scnt, *soff, *qcnt, *qoff;
	int64_t sum_acnt, sum_alen;
	mg_intv_t *sintv, *qintv;

	// count the number of intervals on each segment
	KCALLOC(km, scnt, g->n_seg);
	KCALLOC(km, qcnt, n_seq);
	for (t = 0, max_acnt = 0; t < n_seq; ++t) {
		const mg_gchains_t *gt = gcs[t];
		for (i = 0; i < gt->n_gc; ++i) {
			const mg_gchain_t *gc = &gt->gc[i];
			if (gc->id != gc->parent || gc->flt) continue; // flt: suppressed by an end event
			if (gc->blen < min_depth_len || gc->mapq < min_mapq) continue;
			if (gc->n_anchor > max_acnt) max_acnt = gc->n_anchor;
			++qcnt[t];
			for (j = 0; j < gc->cnt; ++j)
				++scnt[gt->lc[gc->off + j].v>>1];
		}
	}
	if (max_acnt == 0) { // no gchain
		kfree(km, scnt); kfree(km, qcnt);
		return 0;
	}

	// compute soff[] and qoff[]
	KMALLOC(km, soff, g->n_seg + 1);
	KMALLOC(km, qoff, n_seq + 1);
	for (soff[0] = 0, i = 1; i <= g->n_seg; ++i)
		soff[i] = soff[i - 1] + scnt[i - 1];
	for (qoff[0] = 0, i = 1; i <= n_seq; ++i)
		qoff[i] = qoff[i - 1] + qcnt[i - 1];

	// populate the interval list
	memset(scnt, 0, 4 * g->n_seg);
	memset(qcnt, 0, 4 * n_seq);
	KMALLOC(km, sintv, soff[g->n_seg]);
	KMALLOC(km, qintv, qoff[n_seq]);
	sum_acnt = sum_alen = 0;
	for (t = 0; t < n_seq; ++t) {
		const mg_gchains_t *gt = gcs[t];
		for (i = 0; i < gt->n_gc; ++i) {
			const mg_gchain_t *gc = &gt->gc[i];
			mg_intv_t *p;
			int32_t cid;
			if (gc->id != gc->parent || gc->flt) continue; // flt: suppressed by an end event
			if (gc->blen < min_depth_len || gc->mapq < min_mapq) continue;
			cid = qoff[t] + qcnt[t];
			p = &qintv[cid];
			++qcnt[t];
			p->st = gc->qs, p->en = gc->qe, p->rev = 0, p->far = -1, p->i = -1;
			for (j = 0; j < gc->cnt; ++j) {
				const mg_llchain_t *lc = &gt->lc[gc->off + j];
				int32_t rs, re, tmp;
				if (lc->cnt > 0) { // compute start and end on the forward strand on the segment
					const mg128_t *qs = &gt->a[lc->off];
					const mg128_t *qe = &gt->a[lc->off + lc->cnt - 1];
					int32_t rs0 = (int32_t)qs->x + 1 - (int32_t)(qs->y>>32&0xff);
					int32_t re0 = (int32_t)qe->x;
					assert(rs0 >= 0 && re0 > rs0 && re0 < g->seg[lc->v>>1].len);
					sum_alen += re0 - rs0, sum_acnt += (qe->x>>32) - (qs->x>>32) + 1;
					rs = 0, re = g->seg[lc->v>>1].len;
					if (j == 0) rs = gc->p? gc->p->ss : rs0;
					if (j == gc->cnt - 1) re = gc->p? gc->p->ee : re0;
					if (lc->v&1) // swap rs and re
						tmp = rs, rs = g->seg[lc->v>>1].len - re, re = g->seg[lc->v>>1].len - tmp;
				} else rs = 0, re = g->seg[lc->v>>1].len;
				p = &sintv[soff[lc->v>>1] + scnt[lc->v>>1]];
				++scnt[lc->v>>1];
				p->st = rs, p->en = re, p->rev = lc->v&1, p->far = -1, p->i = cid; // the chain this interval comes from
			}
		}
	}
	*a_dens = (double)sum_acnt / sum_alen;

	// sort and index intervals
	for (i = 0; i < g->n_seg; ++i) {
		assert(soff[i+1] - soff[i] == scnt[i]);
		mg_intv_index(soff[i+1] - soff[i], &sintv[soff[i]]);
	}
	kfree(km, scnt);
	for (i = 0; i < n_seq; ++i) {
		assert(qoff[i+1] - qoff[i] == qcnt[i]);
		mg_intv_index(qoff[i+1] - qoff[i], &qintv[qoff[i]]);
	}
	kfree(km, qcnt);

	*sintv_ = sintv, *qintv_ = qintv;
	*soff_ = soff, *qoff_ = qoff;
	return max_acnt;
}

/**********************
 * Graph augmentation *
 **********************/

void mg_ggsimple(void *km, const mg_ggopt_t *opt, gfa_t *g, int32_t n_seq, const mg_bseq1_t *seq, mg_gchains_t *const* gcs)
{
	int32_t t, i, j, *soff, *qoff, max_acnt, *sc, m_ovlp = 0, *ovlp = 0, n_ins, m_ins, n_inv;
	int32_t l_pseq, m_pseq;
	uint64_t *meta;
	mg_intv_t *sintv, *qintv;
	double a_dens;
	gfa_ins_t *ins;
	char *pseq;

	max_acnt = mg_gc_index(km, opt->min_mapq, opt->min_map_len, opt->min_depth_len, g, n_seq, gcs, &a_dens, &soff, &qoff, &sintv, &qintv);
	if (max_acnt == 0) return;

	// extract poorly regions
	m_pseq = l_pseq = 0, pseq = 0;
	m_ins = n_ins = 0, ins = 0;
	n_inv = 0;
	KMALLOC(km, sc, max_acnt);
	KMALLOC(km, meta, max_acnt);
	for (t = 0; t < n_seq; ++t) {
		const mg_gchains_t *gt = gcs[t];
		for (i = 0; i < gt->n_gc; ++i) {
			const mg_gchain_t *gc = &gt->gc[i];
			int32_t off_a, off_l, n_ss, far_q;
			mg_msseg_t *ss;
			if (gc->id != gc->parent) continue;
			if (gc->blen < opt->min_map_len || gc->mapq < opt->min_mapq) continue;
			assert(gc->cnt > 0);

			// fill sc[]. This part achieves a similar goal to the one in mg_gchain_extra(). It makes more assumptions, but is logically simpler.
			off_l = gc->off;
			off_a = gt->lc[off_l].off + 1;
			far_q = 0;
			for (j = 1; j < gc->n_anchor; ++j, ++off_a) {
				const mg128_t *q = &gt->a[off_a - 1], *p = &gt->a[off_a];
				const mg_llchain_t *lc = &gt->lc[off_l];
				int32_t s, ed = -1, off_l0 = off_l, pd, qd = (int32_t)p->y - (int32_t)q->y, c = (int32_t)(p->x>>32) - (int32_t)(q->x>>32) - 1;
				if ((int32_t)q->y > far_q) far_q = (int32_t)q->y; // far_q keeps the rightmost query position seen so far
				if (off_a == lc->off + lc->cnt) { // we are at the end of the current lchain
					pd = g->seg[lc->v>>1].len - (int32_t)q->x - 1;
					for (++off_l; off_l < gc->off + gc->cnt && gt->lc[off_l].cnt == 0; ++off_l)
						pd += g->seg[gt->lc[off_l].v>>1].len;
					assert(off_l < gc->off + gc->cnt);
					if (gt->lc[off_l].ed >= 0) ed = gt->lc[off_l].ed;
					pd += (int32_t)p->x + 1;
				} else pd = (int32_t)p->x - (int32_t)q->x;
				if ((opt->flag&MG_G_NO_QOVLP) && (int32_t)p->y < far_q) s = 1; // query overlap
				else if (pd == qd && c == 0) s = -opt->match_pen;
				else if (ed >= 0) {
					int32_t min_d = pd < qd? pd : qd;
					double t = 1. / (1.01 - opt->ggs_max_iden);
					if (t > 10.) t = 10.;
					s = (int32_t)(ed * t - min_d);
				} else if (pd > qd) {
					double x = qd * a_dens;
					x = x > c? x : c;
					s = (int32_t)(x + (pd - qd) * a_dens + .499);
				} else {
					s = (int32_t)(qd * a_dens + .499);
					s = s > c? s : c;
				}
				sc[j - 1] = s;
				meta[j-1] = (uint64_t)pd<<32 | off_l0;
			}

			// get regions to insert
			ss = mg_mss_all(0, gc->n_anchor - 1, sc, 10, 0, &n_ss);
			off_a = gt->lc[gc->off].off;
			for (j = 0; j < n_ss; ++j) {
				const mg128_t *p, *q;
				int32_t st, en, ls, le, span, pd, k, n_ovlp, min_len, is_inv = 0;
				gfa_ins_t I;

				// find the initial positions
				min_len = opt->ggs_min_end_cnt > 0? opt->ggs_min_end_cnt : 0;
				if (min_len < ss[j].sc * opt->ggs_min_end_frac) min_len = ss[j].sc * opt->ggs_min_end_frac;
				if (ss[j].st <= min_len || ss[j].en >= gc->n_anchor - 1 - min_len) continue; // too close to ends
				st = ss[j].st, en = ss[j].en;
				q = &gt->a[off_a + st];
				p = &gt->a[off_a + en];
				span = p->y>>32&0xff;
				I.ctg = t;
				ls = (int32_t)meta[st], le = (int32_t)meta[en]; // first and last lchain; CLOSED interval
				assert(ls <= le);
				I.v[0] = gt->lc[ls].v;
				I.v[1] = gt->lc[le].v;
				I.voff[0] = (int32_t)q->x + 1 - span;
				I.voff[1] = (int32_t)p->x + 1;
				I.coff[0] = (int32_t)q->y + 1 - span;
				I.coff[1] = (int32_t)p->y + 1;
				assert(I.voff[0] <= g->seg[I.v[0]>>1].len);
				assert(I.voff[1] <= g->seg[I.v[1]>>1].len);
				for (k = st, pd = span; k < en; ++k)
					pd += meta[k]>>32;

				if (I.coff[0] > I.coff[1]) {
					if (mg_verbose >= 2 && pd + (I.coff[0] - I.coff[1]) >= opt->min_var_len)
						fprintf(stderr, "[W::%s] query overlap on gchain %d: [%c%s:%d,%c%s:%d|%d] <=> %s:[%d,%d|%d]\n", __func__, t, "><"[I.v[0]&1], g->seg[I.v[0]>>1].name, I.voff[0], "><"[I.v[1]&1], g->seg[I.v[1]>>1].name, I.voff[1], pd, seq[t].name, I.coff[0], I.coff[1], I.coff[1] - I.coff[0]);
					continue; // such overlap can't be properly resolved
				}
				pd -= gfa_ins_adj(g, opt->ggs_shrink_pen, &I, seq[t].seq);

				min_len = pd > I.coff[1] - I.coff[0]? pd : I.coff[1] - I.coff[0];
				if (I.coff[0] <= min_len || I.coff[1] >= seq[t].l_seq - min_len) continue; // test if the event is close to ends again

				// filtering
				if (I.coff[1] - I.coff[0] < opt->min_var_len && pd < opt->min_var_len)
					continue;
				for (k = I.coff[0]; k < I.coff[1]; ++k) { // test ambiguous bases
					int c = seq[t].seq[k];
					if (c == 'n' || c == 'N') break;
				}
				if (k != I.coff[1]) continue; // no ambiguous bases on the insert
				n_ovlp = mg_intv_overlap(km, qoff[t+1] - qoff[t], &qintv[qoff[t]], I.coff[0], I.coff[1], &ovlp, &m_ovlp); // test overlapping on the query
				if (n_ovlp == 0) fprintf(stderr, "[W::%s] query interval %s:%d-%d is not covered\n", __func__, seq[t].name, I.coff[0], I.coff[1]);
				if (n_ovlp != 1) continue;
				for (k = ls; k <= le; ++k) { // find other mappings overlapping with the insert on the graph
					uint32_t v = gt->lc[k].v, len = g->seg[v>>1].len;
					int32_t s = 0, e = len, tmp;
					if (k == ls) s = (int32_t)gt->a[off_a+st].x + 1 - (int32_t)(gt->a[off_a+st].y>>32&0xff);
					if (k == le) e = (int32_t)gt->a[off_a+en].x + 1;
					if (v&1) tmp = s, s = len - e, e = len - tmp;
					n_ovlp = mg_intv_overlap(km, soff[(v>>1)+1] - soff[v>>1], &sintv[soff[v>>1]], s, e, &ovlp, &m_ovlp);
					if (n_ovlp == 0) fprintf(stderr, "[W::%s] graph interval %s:%d-%d is not covered by %s:%d-%d\n", __func__, g->seg[v>>1].name, s, e, seq[t].name, I.coff[0], I.coff[1]); // this should be an assert()
					if (n_ovlp != 1) break;
				}
				if (k <= le) continue;
				if (pd - (I.coff[1] - I.coff[0]) < opt->min_var_len && (I.coff[1] - I.coff[0]) - pd < opt->min_var_len) { // if length difference > min_var_len, just insert
					int32_t qd = I.coff[1] - I.coff[0], mlen, blen, score;
					l_pseq = mg_path2seq(km, g, gt, ls, le, I.voff, &pseq, &m_pseq);
					score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
					if (score > 0) {
						if (mlen > blen * opt->ggs_max_iden) continue; // make sure k-mer identity is small enough
						if (blen - mlen < opt->min_var_len * opt->ggs_max_iden) continue;
					} else if (!(opt->flag & MG_G_NO_INV)) {
						mg_revcomp_seq(l_pseq, pseq);
						score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
						if (score > 0 && mlen > blen * opt->ggs_min_inv_iden) is_inv = 1;
					}
				}
				if (mg_dbg_flag & MG_DBG_INSERT) {
					int32_t mlen, blen, score, qd = I.coff[1] - I.coff[0];
					l_pseq = mg_path2seq(km, g, gt, ls, le, I.voff, &pseq, &m_pseq);
					fprintf(stderr, "IN\t[%c%s:%d,%c%s:%d|%d] <=> %s:[%d,%d|%d] inv:%d\n", "><"[I.v[0]&1], g->seg[I.v[0]>>1].name, I.voff[0], "><"[I.v[1]&1], g->seg[I.v[1]>>1].name, I.voff[1], pd, seq[t].name, I.coff[0], I.coff[1], I.coff[1] - I.coff[0], is_inv);
					fprintf(stderr, "IP\t%s\nIQ\t", pseq);
					fwrite(&seq[t].seq[I.coff[0]], 1, qd, stderr);
					if (pd - qd < opt->min_var_len && qd - pd < opt->min_var_len) {
						score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
					} else score = -1, mlen = 0, blen = pd > qd? pd : qd;
					fprintf(stderr, "\nIS\t%d==%d\tnwcmp:%d\tmlen:%d\tblen:%d\n", pd, l_pseq, score, mlen, blen);
				}
				if (is_inv) { // turn one inversion to two events
					gfa_ins_t I_inv[2];
					I_inv[0].ctg = I_inv[1].ctg = I.ctg;
					// the first event
					I_inv[0].coff[0] = I_inv[0].coff[1] = I.coff[0];
					I_inv[0].v[0] = I.v[0];
					I_inv[0].voff[0] = I.voff[0];
					I_inv[0].v[1] = I.v[1]^1;
					I_inv[0].voff[1] = g->seg[I.v[1]>>1].len - I.voff[1];
					// the second event
					I_inv[1].coff[0] = I_inv[1].coff[1] = I.coff[1];
					I_inv[1].v[0] = I.v[0]^1;
					I_inv[1].voff[0] = g->seg[I.v[0]>>1].len - I.voff[0];
					I_inv[1].v[1] = I.v[1];
					I_inv[1].voff[1] = I.voff[1];
					// insert
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I_inv[0];
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I_inv[1];
					++n_inv;
				} else {
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I;
				}
			}
			kfree(0, ss);
		}
	}
	kfree(km, pseq);
	kfree(km, ovlp);
	kfree(km, sc);
	kfree(km, meta);
	kfree(km, soff); kfree(km, qoff);
	kfree(km, sintv); kfree(km, qintv);

	if (n_ins > 0) {
		char **names, **seqs;
		KMALLOC(km, names, n_seq);
		KMALLOC(km, seqs, n_seq);
		for (i = 0; i < n_seq; ++i)
			names[i] = seq[i].name, seqs[i] = seq[i].seq;
		n_ins = gfa_ins_filter(g, n_ins, ins);
		gfa_augment(g, n_ins, ins, n_seq, (const char*const*)names, (const char*const*)seqs);
		kfree(km, ins);
		kfree(km, names);
		kfree(km, seqs);
	}
	if (mg_verbose >= 3)
		fprintf(stderr, "[M::%s::%.3f*%.2f] inserted %d events, including %d inversions\n", __func__,
				realtime() - mg_realtime0, cputime() / (realtime() - mg_realtime0), n_ins, n_inv);
}

/**********************
 * Graph augmentation *
 **********************/

typedef struct {
	int32_t lc, vo, qo, po, len, op, sc;
} ed_intv_t;

static int32_t gg_count_intv(const gfa_t *g, const mg_gchains_t *gt, int32_t i)
{
	const mg_gchain_t *gc = &gt->gc[i];
	int32_t j, l = gc->off, x = gc->ps, n = 0;
	assert(gc->p);
	for (j = 0; j < gc->p->n_cigar; ++j) {
		int32_t op = gc->p->cigar[j]&0xf, len = gc->p->cigar[j]>>4, rl = len;
		assert(op == 1 || op == 2 || op == 7 || op == 8);
		if (op == 2 || op == 7 || op == 8) {
			while (x + rl > g->seg[gt->lc[l].v>>1].len) {
				rl -= g->seg[gt->lc[l].v>>1].len - x;
				++n, ++l, x = 0;
			}
			x += rl;
		}
		++n;
	}
	return n;
}

static void gg_write_intv(const gfa_t *g, const mg_gchains_t *gt, int32_t i, ed_intv_t *intv)
{
	const mg_gchain_t *gc = &gt->gc[i];
	int32_t j, l = gc->off, pl = 0, x = gc->ps, y = gc->qs, n = 0;
	ed_intv_t *p;
	assert(gc->p);
	for (j = 0; j < gc->p->n_cigar; ++j) {
		int32_t op = gc->p->cigar[j]&0xf, len = gc->p->cigar[j]>>4, rl = len;
		if (op == 2 || op == 7 || op == 8) {
			while (x + rl > g->seg[gt->lc[l].v>>1].len) {
				p = &intv[n++];
				p->lc = l, p->vo = x, p->qo = y, p->po = pl, p->len = g->seg[gt->lc[l].v>>1].len - x, p->op = op;
				if (op == 7 || op == 8) y += p->len;
				rl -= p->len, pl += p->len, ++l, x = 0;
			}
		}
		p = &intv[n++];
		p->lc = l, p->vo = x, p->qo = y, p->po = pl, p->len = rl, p->op = op;
		if (op == 7 || op == 8) x += rl, y += rl, pl += rl;
		else if (op == 1) y += rl;
		else if (op == 2) x += rl, pl += rl;
	}
	assert(y == gc->qe && pl == gc->pe - gc->ps);
}

static void gg_score_intv(int32_t n_intv, ed_intv_t *intv)
{
	int32_t j;
	for (j = 0; j < n_intv; ++j) {
		int32_t s;
		if (intv[j].op == 7)
			s = intv[j].len >= 10? -intv[j].len : 0;
		else s = intv[j].len;
		intv[j].sc = s;
	}
}

static void gg_merge_seg(const ed_intv_t *intv, int32_t n_ss, mg_msseg_t *ss)
{
	int32_t j0, j;
	for (j0 = 0, j = 1; j < n_ss; ++j) {
		mg_msseg_t *s0 = &ss[j0], *s1 = &ss[j];
		int32_t i, mid = 0;
		for (i = s0->en + 1; i < s1->st; ++i)
			mid += intv[i].sc;
		//fprintf(stderr, "XX\t%d\t%d\t%d\t%d\t%d\t%d\n", j, s0->sc, mid, s1->sc, s0->en+1, s1->st);
		if (-mid < s0->sc * 0.2 && -mid < s1->sc * 0.2) { // FIXME: mid is sometimes 0
			s0->en = s1->en, s0->sc += s1->sc + mid;
			s1->st = s1->en, s1->sc = 0;
		} else j0 = j;
	}
}

/**************
 * End events *
 **************/

// The next vertex walking outward from v: the continuation of v's own stable sequence (the reference, or an alt such
// as an earlier end event's tip that later inserts have split) if there is one, else the only arc.  At a tip, *is_tip
// is set; (uint32_t)-1 is returned there and where the way on is ambiguous.
static uint32_t gg_tip_next(const gfa_t *g, uint32_t v, int *is_tip)
{
	uint32_t i, n = gfa_arc_n(g, v), n_live = 0, w = (uint32_t)-1, w_ref = (uint32_t)-1;
	const gfa_arc_t *a = gfa_arc_a(g, v);
	const gfa_seg_t *s = &g->seg[v>>1];
	*is_tip = 0;
	for (i = 0; i < n; ++i) {
		const gfa_seg_t *t;
		if (a[i].del) continue;
		++n_live, w = a[i].w;
		t = &g->seg[a[i].w>>1];
		if (s->rank == t->rank && s->snid == t->snid && (v&1) == (a[i].w&1)
			&& ((v&1) == 0? t->soff == s->soff + s->len : s->soff == t->soff + t->len))
			w_ref = a[i].w;
	}
	if (n_live == 0) {
		*is_tip = 1;
		return (uint32_t)-1;
	}
	if (w_ref != (uint32_t)-1) return w_ref;
	return n_live == 1? w : (uint32_t)-1;
}

typedef struct { int32_t seg, st, en; } gg_span_t; // a forward-strand interval on a segment

static inline void gg_span_push(void *km, const gfa_t *g, uint32_t w, int32_t woff, gg_span_t **a, int32_t *n, int32_t *m)
{
	int32_t len = g->seg[w>>1].len;
	if (*n == *m) KEXPAND(km, *a, *m);
	(*a)[*n].seg = w>>1;
	if ((w&1) == 0) (*a)[*n].st = woff, (*a)[*n].en = len;
	else (*a)[*n].st = 0, (*a)[*n].en = len - woff;
	++*n;
}

// distance from offset woff on vertex w to the tip reached by walking outward; -1 if it is beyond max_d or ambiguous.
// The stretch walked is put in *sp, as forward-strand intervals on segments.
static int32_t gg_dist_to_tip(void *km, const gfa_t *g, uint32_t w, int32_t woff, int32_t max_d, gg_span_t **sp, int32_t *n_sp, int32_t *m_sp)
{
	int32_t d = g->seg[w>>1].len - woff, n_step = 0;
	*n_sp = 0;
	gg_span_push(km, g, w, woff, sp, n_sp, m_sp);
	while (d <= max_d && n_step++ < 1000000) {
		int is_tip;
		uint32_t u = gg_tip_next(g, w, &is_tip);
		if (is_tip) return d;
		if (u == (uint32_t)-1) return -1;
		w = u, d += g->seg[w>>1].len;
		gg_span_push(km, g, w, 0, sp, n_sp, m_sp);
	}
	return -1;
}

// whether chain gc covers any of the spans, on the forward strand of their segments (the way mg_gc_index() places it)
static int gg_chain_on_spans(const gfa_t *g, const mg_gchains_t *gt, const mg_gchain_t *gc, const gg_span_t *sp, int32_t n_sp)
{
	int32_t j, k;
	for (j = 0; j < gc->cnt; ++j) {
		uint32_t v = gt->lc[gc->off + j].v;
		int32_t len = g->seg[v>>1].len, st = 0, en = len, tmp;
		if (gc->p && j == 0) st = gc->p->ss;
		if (gc->p && j == gc->cnt - 1) en = gc->p->ee;
		if (v&1) tmp = st, st = len - en, en = len - tmp;
		for (k = 0; k < n_sp; ++k)
			if (sp[k].seg == (int32_t)(v>>1) && st < sp[k].en && sp[k].st < en) return 1;
	}
	return 0;
}

// up to lp bases of the graph walking outward from offset woff on vertex w, upper-cased
static int32_t gg_tip_seq(void *km, const gfa_t *g, uint32_t w, int32_t woff, int32_t lp, char **buf, int32_t *cap)
{
	int32_t l = 0, n_step = 0;
	if (*cap < lp + 1) {
		*cap = lp + 1;
		KREALLOC(km, *buf, *cap);
	}
	while (l < lp && n_step++ < 1000000) {
		const gfa_seg_t *s = &g->seg[w>>1];
		int32_t j;
		int is_tip;
		uint32_t u;
		for (j = woff; j < s->len && l < lp; ++j)
			(*buf)[l++] = toupper((w&1) == 0? s->seq[j] : gfa_comp_table[(uint8_t)s->seq[s->len - 1 - j]]);
		u = gg_tip_next(g, w, &is_tip);
		if (is_tip || u == (uint32_t)-1) break;
		w = u, woff = 0;
	}
	(*buf)[l] = 0;
	return l;
}

// telomere repeats in s[st,en): the right end of a sequence reads TTAGGG, the left end CCCTAA
static int32_t gg_telo_cnt(const char *s, int32_t st, int32_t en, int right)
{
	const char *m = right? "TTAGGG" : "CCCTAA";
	int32_t i, n = 0;
	for (i = st; i + 6 <= en; ++i)
		if (memcmp(&s[i], m, 6) == 0) ++n, i += 5;
	return n;
}

// the length of the telomeric run at one end of s: 100bp windows, from the end inward, that are at least half repeat
static int32_t gg_telo_len(const char *s, int32_t l, int right)
{
	int32_t x;
	for (x = 0; x + 100 <= l; x += 100) {
		int32_t st = right? l - x - 100 : x;
		if (gg_telo_cnt(s, st, st + 100, right) * 6 * 2 < 100) break;
	}
	return x;
}

typedef struct {
	gfa_ins_t ins;
	gg_span_t at;           // the graph next to the attachment, inward
	uint64_t key;           // query<<32 | chain<<1 | side
	int32_t ovh, telo, d;   // the overhang, its telomeric run and the distance from the attachment to the tip
	int32_t sec_off, n_sec; // the chains of the query that the event suppresses: sec[sec_off, sec_off+n_sec)
} gg_end_t;

typedef struct { // the end events of a round, and buffers
	int32_t n_ev, m_ev, n_sec, m_sec, n_sp, m_sp, m_pseq, m_qseq;
	gg_end_t *ev;
	int32_t *sec;
	gg_span_t *sp;
	char *pseq, *qseq;
} gg_endbuf_t;

// the end events of query t, each tested against the chains of the query, but those in vk[], vetoed in an earlier round;
// the chains an event suppresses are flagged (flt) as it is found
static void gg_end_query(void *km, const mg_ggopt_t *opt, const gfa_t *g, int32_t t, const mg_bseq1_t *seq1, mg_gchains_t *gt,
						 int32_t n_vk, const uint64_t *vk, int dbg, gg_endbuf_t *b)
{
	const char *s = seq1->seq;
	int32_t i, k, side, l_seq = seq1->l_seq;
	for (i = 0; i < gt->n_gc; ++i) {
		mg_gchain_t *gc = &gt->gc[i];
		if (gc->id != gc->parent || gc->flt) continue;
		if (gc->p == 0 || gc->blen < opt->min_map_len || gc->mapq < opt->min_mapq) continue;
		for (side = 0; side < 2; ++side) { // 0: [qe,l_seq) past the last anchor; 1: [0,qs) before the first
			uint64_t key = (uint64_t)t<<32 | (uint64_t)i<<1 | side;
			gfa_ins_t I;
			gg_span_t at;
			gg_end_t *e;
			uint32_t w, va;
			int32_t woff, d, ovh, telo = 0, lp, l_pseq, i2, *sec1, n_sec, veto, mlen, blen, score, diff, longer;
			for (k = 0; k < n_vk && vk[k] != key; ++k);
			if (k < n_vk) continue; // vetoed by another query's chain
			I.ctg = t;
			if (side == 0) {
				I.v[0] = gt->lc[gc->off + gc->cnt - 1].v, I.voff[0] = gc->p->ee;
				I.v[1] = GFA_INS_NONE, I.voff[1] = -1;
				I.coff[0] = gc->qe, I.coff[1] = l_seq;
			} else {
				I.v[1] = gt->lc[gc->off].v, I.voff[1] = gc->p->ss;
				I.v[0] = GFA_INS_NONE, I.voff[0] = -1;
				I.coff[0] = 0, I.coff[1] = gc->qs;
			}
#define GG_END_SKIP(why) { if (dbg) fprintf(stderr, "IX\t%s:[%d,%d) side:%d %s\n", seq1->name, I.coff[0], I.coff[1], side, (why)); continue; }
			ovh = I.coff[1] - I.coff[0];
			if (ovh < opt->min_var_len) continue;
			if (ovh < opt->ggs_tip_min || ovh > opt->ggs_tip_max) GG_END_SKIP("length");
			if (opt->ggs_tip_telo > 0) { // the query end must be a telomere
				int32_t win = opt->ggs_tip_telo < l_seq? opt->ggs_tip_telo : l_seq;
				int32_t st = side == 0? l_seq - win : 0;
				if (gg_telo_cnt(s, st, st + win, side == 0) * 6 * 2 < win) GG_END_SKIP("no-telomere");
				telo = gg_telo_len(s, l_seq, side == 0);
			}
			for (k = I.coff[0]; k < I.coff[1]; ++k) // no ambiguous bases
				if (s[k] == 'N' || s[k] == 'n') break;
			if (k != I.coff[1]) GG_END_SKIP("N");
			ovh -= gfa_ins_adj1(g, opt->ggs_shrink_pen, &I, s);
			if (ovh < opt->min_var_len) GG_END_SKIP("shrunk");
			if (ovh - telo < opt->ggs_tip_min) GG_END_SKIP("telomere-only"); // little more than a longer telomere
			if (side == 0) w = I.v[0], woff = I.voff[0];
			else w = I.v[1]^1, woff = g->seg[I.v[1]>>1].len - I.voff[1];
			d = gg_dist_to_tip(km, g, w, woff, opt->ggs_tip_dist, &b->sp, &b->n_sp, &b->m_sp);
			if (d <= 0) GG_END_SKIP(d == 0? "at-end" : "not-near-end"); // too far from an end, ambiguous, or right at the end (an extension, not a fork)
			if (b->n_sec + gt->n_gc > b->m_sec) {
				b->m_sec = b->n_sec + gt->n_gc;
				KREALLOC(km, b->sec, b->m_sec);
			}
			sec1 = &b->sec[b->n_sec]; // the chains this event would suppress
			for (i2 = 0, n_sec = 0, veto = 0; i2 < gt->n_gc; ++i2) { // the query's other chains
				mg_gchain_t *c2 = &gt->gc[i2];
				int32_t ov, conf;
				if (i2 == i || c2->id != c2->parent || c2->flt) continue;
				conf = c2->blen >= opt->min_depth_len && c2->mapq >= opt->min_mapq;
				if (conf && gg_chain_on_spans(g, gt, c2, b->sp, b->n_sp)) { // the query itself aligns to the end walked to
					veto = 2;
					break;
				}
				ov = (c2->qe < I.coff[1]? c2->qe : I.coff[1]) - (c2->qs > I.coff[0]? c2->qs : I.coff[0]);
				if (ov <= 0) continue;
				if (i2 > i && ov > 0.5 * (c2->qe - c2->qs)) sec1[n_sec++] = i2; // gc->gc[] is sorted by score
				else if (i2 < i || conf) {
					veto = 1;
					break;
				}
			}
			if (veto) GG_END_SKIP(veto == 2? "on-walk" : "veto");
			// as for other events, no other confident chain of the batch may cover the attachment: test the 1kb inward
			// of it, as the shrink can move the attachment past the first anchor of an identical chain.  The query's
			// own chains are tested here, the other queries' ones by gg_end_events()
			va = side == 0? I.v[0] : I.v[1];
			{
				int32_t len = g->seg[va>>1].len, st, en, tmp;
				if (side == 0) st = I.voff[0] - 1000, en = I.voff[0];
				else st = I.voff[1], en = I.voff[1] + 1000;
				if (st < 0) st = 0;
				if (en > len) en = len;
				if (va&1) tmp = st, st = len - en, en = len - tmp;
				at.seg = va>>1, at.st = st, at.en = en;
			}
			for (i2 = 0; i2 < gt->n_gc; ++i2) {
				const mg_gchain_t *c3 = &gt->gc[i2];
				if (i2 == i || c3->id != c3->parent || c3->flt) continue;
				if (c3->blen < opt->min_depth_len || c3->mapq < opt->min_mapq) continue;
				for (k = 0; k < n_sec && sec1[k] != i2; ++k);
				if (k < n_sec) continue; // about to be suppressed
				if (gg_chain_on_spans(g, gt, c3, &at, 1)) break;
			}
			if (i2 < gt->n_gc) GG_END_SKIP("multi-cover");
			// where the overhang and the reference's remaining end are of similar length, they must differ
			diff = ovh > d? ovh - d : d - ovh;
			longer = ovh > d? ovh : d;
			if (diff < opt->min_var_len || diff < longer / 10) {
				lp = ovh < d? ovh : d;
				if (lp > 10000) lp = 10000;
				l_pseq = gg_tip_seq(km, g, w, woff, lp, &b->pseq, &b->m_pseq);
				if (b->m_qseq < lp + 1) {
					b->m_qseq = lp + 1;
					KREALLOC(km, b->qseq, b->m_qseq);
				}
				if (side == 0) memcpy(b->qseq, &s[I.coff[0]], lp);
				else for (k = 0; k < lp; ++k) b->qseq[k] = gfa_comp_table[(uint8_t)s[I.coff[1] - 1 - k]];
				b->qseq[lp] = 0;
				score = mg_wfa_cmp(km, l_pseq, b->pseq, lp, b->qseq, 5000, &mlen, &blen);
				if (score > 0 && mlen > blen * opt->ggs_max_iden) GG_END_SKIP("same-as-ref-end");
			}
#undef GG_END_SKIP
			for (k = 0; k < n_sec; ++k) // so that the query's later events do not see them
				gt->gc[sec1[k]].flt = 1;
			if (b->n_ev == b->m_ev) KEXPAND(km, b->ev, b->m_ev);
			e = &b->ev[b->n_ev++];
			e->ins = I, e->at = at, e->key = key, e->ovh = ovh, e->telo = telo, e->d = d;
			e->sec_off = b->n_sec, e->n_sec = n_sec;
			b->n_sec += n_sec;
		}
	}
}

// End events.  A confident primary chain's overhang past its last (or before its first) anchor that reaches a
// telomeric query end, where walking on from the attachment along the graph reaches a tip (a chromosome end) within
// ggs_tip_dist, is added as an insert attached on that side only: a new tip forking off next to the reference's own
// end, so a terminal block that differs from the reference's (often a copy of another chromosome's subtelomere) gets
// into the graph.  A lower-scoring chain mostly inside the overhang, such as the overhang aligned to another
// chromosome's end, would have been a secondary had the overhang been aligned; it is suppressed (flt).  The event is
// vetoed by a confident chain that lies on the stretch walked to the tip (the overhang is then the reference's own end,
// with something inserted inside it), by a higher-scoring or confident chain that crosses into the overhang, and by a
// second confident chain covering the attachment.  The chains of other queries are tested last, once every query's
// events have suppressed theirs; the events are then found again without those they vetoed, until none is vetoed.
// Returns the number of events added.
static int32_t gg_end_events(void *km, const mg_ggopt_t *opt, const gfa_t *g, int32_t n_seq, const mg_bseq1_t *seq,
							 mg_gchains_t *const* gcs, gfa_ins_t **ins, int32_t *n_ins, int32_t *m_ins, int32_t *n_sup)
{
	int32_t t, j, k, round, n_end = 0, n_vk = 0, m_vk = 0, n_vk0;
	uint64_t *vk = 0;
	uint8_t *redo;
	gg_endbuf_t b;

	memset(&b, 0, sizeof(b));
	KCALLOC(km, redo, n_seq);
	for (round = 0;; ++round) {
		b.n_ev = b.n_sec = 0;
		for (t = 0; t < n_seq; ++t) {
			gg_end_query(km, opt, g, t, &seq[t], gcs[t], n_vk, vk, (mg_dbg_flag & MG_DBG_INSERT) && (round == 0 || redo[t]), &b);
			redo[t] = 0;
		}
		// the other queries' chains that cover the attachment, tested once every query's events have suppressed theirs
		for (j = 0, n_vk0 = n_vk; j < b.n_ev; ++j) {
			const gg_end_t *e = &b.ev[j];
			int32_t t2, i2 = 0;
			for (t2 = 0; t2 < n_seq; ++t2) {
				const mg_gchains_t *gt2 = gcs[t2];
				if (t2 == e->ins.ctg) continue;
				for (i2 = 0; i2 < gt2->n_gc; ++i2) {
					const mg_gchain_t *c3 = &gt2->gc[i2];
					if (c3->id != c3->parent || c3->flt) continue;
					if (c3->blen < opt->min_depth_len || c3->mapq < opt->min_mapq) continue;
					if (gg_chain_on_spans(g, gt2, c3, &e->at, 1)) break;
				}
				if (i2 < gt2->n_gc) break;
			}
			if (t2 == n_seq) continue;
			if (mg_dbg_flag & MG_DBG_INSERT)
				fprintf(stderr, "IX\t%s:[%d,%d) side:%d %s\n", seq[e->ins.ctg].name, e->ins.coff[0], e->ins.coff[1], (int)(e->key&1), "multi-cover");
			if (n_vk == m_vk) KEXPAND(km, vk, m_vk);
			vk[n_vk++] = e->key;
			redo[e->ins.ctg] = 1;
		}
		if (n_vk == n_vk0) break;
		// a vetoed event gives back the chains it suppressed.  They may cover another event's attachment, change the
		// tests of the other events of their query, or have events of their own, so the round is redone without the
		// vetoed events.  A veto is never undone, so this ends, and every round depends on the vetoes before it, not
		// on the order of the queries
		for (j = 0; j < b.n_ev; ++j)
			for (k = 0; k < b.ev[j].n_sec; ++k)
				gcs[b.ev[j].ins.ctg]->gc[b.sec[b.ev[j].sec_off + k]].flt = 0;
	}
	for (j = 0; j < b.n_ev; ++j) {
		const gg_end_t *e = &b.ev[j];
		const gfa_ins_t *p = &e->ins;
		uint32_t va = p->v[0] != GFA_INS_NONE? p->v[0] : p->v[1];
		if (mg_dbg_flag & MG_DBG_INSERT)
			fprintf(stderr, "IE\t%s:[%d,%d|%d] telo:%d %c%s:%d dist_to_end:%d suppressed:%d\n", seq[p->ctg].name, p->coff[0], p->coff[1], e->ovh, e->telo,
					"><"[va&1], g->seg[va>>1].name, p->v[0] != GFA_INS_NONE? p->voff[0] : p->voff[1], e->d, e->n_sec);
		if (*n_ins == *m_ins) KEXPAND(km, *ins, *m_ins);
		(*ins)[(*n_ins)++] = *p;
		*n_sup += e->n_sec;
		++n_end;
	}
	kfree(km, redo);
	kfree(km, vk);
	kfree(km, b.ev);
	kfree(km, b.sec);
	kfree(km, b.sp);
	kfree(km, b.pseq);
	kfree(km, b.qseq);
	return n_end;
}

void mg_ggsimple_cigar(void *km, const mg_ggopt_t *opt, gfa_t *g, int32_t n_seq, const mg_bseq1_t *seq, mg_gchains_t *const* gcs)
{
	int32_t t, i, *soff = 0, *qoff = 0, max_acnt, m_ovlp = 0, *ovlp = 0, n_ins = 0, m_ins, n_inv, n_end = 0, n_sup = 0;
	int32_t l_pseq, m_pseq;
	mg_intv_t *sintv = 0, *qintv = 0;
	double a_dens;
	gfa_ins_t *ins;
	char *pseq;

	m_ins = n_ins = 0, ins = 0;
	if (opt->flag & MG_G_ENDS) // before indexing, so that the chains they suppress are left out of the index
		n_end = gg_end_events(km, opt, g, n_seq, seq, gcs, &ins, &n_ins, &m_ins, &n_sup);
	max_acnt = mg_gc_index(km, opt->min_mapq, opt->min_map_len, opt->min_depth_len, g, n_seq, gcs, &a_dens, &soff, &qoff, &sintv, &qintv);
	if (max_acnt == 0 && n_ins == 0) return;

	// extract poorly regions
	m_pseq = l_pseq = 0, pseq = 0;
	n_inv = 0;
	for (t = 0; max_acnt > 0 && t < n_seq; ++t) {
		const mg_gchains_t *gt = gcs[t];
		int32_t n_idx = 0; // number of this sequence's chains in the interval index so far
		for (i = 0; i < gt->n_gc; ++i) {
			const mg_gchain_t *gc = &gt->gc[i];
			int32_t j, n_ss, n_intv, *sc, cid = -1;
			ed_intv_t *intv;
			mg_msseg_t *ss;
			if (gc->id != gc->parent || gc->flt) continue; // as mg_gc_index() skips it
			if (gc->blen >= opt->min_depth_len && gc->mapq >= opt->min_mapq) cid = qoff[t] + n_idx++; // as numbered by mg_gc_index()
			if (gc->p == 0 || gc->blen < opt->min_map_len || gc->mapq < opt->min_mapq) continue;
			assert(gc->cnt > 0);

			n_intv = gg_count_intv(g, gt, i);
			KCALLOC(km, intv, n_intv);
			gg_write_intv(g, gt, i, intv);
			gg_score_intv(n_intv, intv);
			KCALLOC(km, sc, n_intv);
			for (j = 0; j < n_intv; ++j) sc[j] = intv[j].sc;
			ss = mg_mss_all(0, n_intv, sc, opt->min_var_len, 2 * opt->min_var_len, &n_ss);
			gg_merge_seg(intv, n_ss, ss);

			// get regions to insert
			for (j = 0; j < n_ss; ++j) {
				int32_t st, en, pd, k, n_ovlp, min_len, is_inv = 0, ls, le;
				gfa_ins_t I;
				ed_intv_t *is, *ie;

				// find the initial positions
				st = ss[j].st, en = ss[j].en; // this is a CLOSED interval
				if (st == en) continue;
				is = &intv[st], ie = &intv[en - 1];
				assert(is->op != 7 && ie->op != 7);

				ls = is->lc, le = ie->lc;
				I.ctg = t;
				I.v[0] = gt->lc[ls].v;
				I.v[1] = gt->lc[le].v;
				I.voff[0] = is->vo;
				I.voff[1] = ie->vo + (ie->op != 1? ie->len : 0);
				I.coff[0] = is->qo;
				I.coff[1] = ie->qo + (ie->op != 2? ie->len : 0);
				assert(I.voff[0] <= g->seg[I.v[0]>>1].len);
				assert(I.voff[1] <= g->seg[I.v[1]>>1].len);

				if (I.voff[0] == 0) { // if an insert starts at pos 0, make it start at the end of the previous vertex in the chain
					assert(ls - 1 >= gc->off);
					I.v[0] = gt->lc[--ls].v;
					I.voff[0] = g->seg[I.v[0]>>1].len;
				}
				if (I.voff[1] == g->seg[I.v[1]>>1].len) { // if an insert ends at the end of the vertex, make it end at the beginning of the next vertex
					assert(le + 1 < gc->off + gc->cnt);
					I.v[1] = gt->lc[++le].v;
					I.voff[1] = 0;
				}

				pd = ie->po + (ie->op != 1? ie->len : 0) - is->po;
				pd -= gfa_ins_adj(g, opt->ggs_shrink_pen, &I, seq[t].seq);

				min_len = pd > I.coff[1] - I.coff[0]? pd : I.coff[1] - I.coff[0];
				if (I.coff[0] <= min_len || I.coff[1] >= seq[t].l_seq - min_len) continue; // test if the event is close to ends again

				// filtering
				if (I.coff[1] - I.coff[0] < opt->min_var_len && pd < opt->min_var_len)
					continue;
				for (k = I.coff[0]; k < I.coff[1]; ++k) { // test ambiguous bases
					int c = seq[t].seq[k];
					if (c == 'n' || c == 'N') break;
				}
				if (k != I.coff[1]) continue; // no ambiguous bases on the insert
				n_ovlp = mg_intv_overlap(km, qoff[t+1] - qoff[t], &qintv[qoff[t]], I.coff[0], I.coff[1], &ovlp, &m_ovlp); // test overlapping on the query
				if (n_ovlp == 0) fprintf(stderr, "[W::%s] query interval %s:%d-%d is not covered\n", __func__, seq[t].name, I.coff[0], I.coff[1]);
				if (n_ovlp != 1) continue;
				for (k = is->lc; k <= ie->lc; ++k) { // find other mappings overlapping with the insert on the graph
					uint32_t v = gt->lc[k].v, len = g->seg[v>>1].len;
					int32_t s = 0, e = len, tmp;
					if (k == is->lc) s = is->vo;
					if (k == ie->lc) e = ie->vo + (ie->op != 1? ie->len : 0);
					if (v&1) tmp = s, s = len - e, e = len - tmp;
					if (s == e) {
						if (s == 0) ++e;
						else --s;
					}
					n_ovlp = mg_intv_overlap(km, soff[(v>>1)+1] - soff[v>>1], &sintv[soff[v>>1]], s, e, &ovlp, &m_ovlp);
					if (n_ovlp == 0) fprintf(stderr, "[W::%s] graph interval %c%s:%d-%d is not covered by %s:%d-%d\n", __func__, "><"[v&1], g->seg[v>>1].name, s, e, seq[t].name, I.coff[0], I.coff[1]); // this should be an assert()
					if (n_ovlp > 1 && (opt->flag & MG_G_SELF_OVLP) && cid >= 0) { // a chain that passes a segment twice (e.g. through inverted copies) only overlaps itself
						int32_t q;
						for (q = 0; q < n_ovlp; ++q)
							if (sintv[soff[v>>1] + ovlp[q]].i != cid) break;
						if (q == n_ovlp) n_ovlp = 1;
					}
					if (n_ovlp != 1) break;
				}
				if (k <= ie->lc) continue;
				if (pd - (I.coff[1] - I.coff[0]) < opt->min_var_len && (I.coff[1] - I.coff[0]) - pd < opt->min_var_len) { // if length difference > min_var_len, just insert
					int32_t qd = I.coff[1] - I.coff[0], mlen, blen, score = 0;
					l_pseq = mg_path2seq(km, g, gt, ls, le, I.voff, &pseq, &m_pseq);
					score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
					if (score > 0) {
						if (mlen > blen * opt->ggs_max_iden) continue; // make sure k-mer identity is small enough
						if (blen - mlen < opt->min_var_len * opt->ggs_max_iden) continue;
					} else if (!(opt->flag & MG_G_NO_INV)) {
						mg_revcomp_seq(l_pseq, pseq);
						score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
						if (score > 0 && mlen > blen * opt->ggs_min_inv_iden) is_inv = 1;
					}
				}
				if (mg_dbg_flag & MG_DBG_INSERT) {
					int32_t mlen, blen, score, qd = I.coff[1] - I.coff[0];
					l_pseq = mg_path2seq(km, g, gt, ls, le, I.voff, &pseq, &m_pseq);
					fprintf(stderr, "IN\t[%c%s:%d,%c%s:%d|%d] <=> %s:[%d,%d|%d] inv:%d\n", "><"[I.v[0]&1], g->seg[I.v[0]>>1].name, I.voff[0], "><"[I.v[1]&1], g->seg[I.v[1]>>1].name, I.voff[1], pd, seq[t].name, I.coff[0], I.coff[1], I.coff[1] - I.coff[0], is_inv);
					fprintf(stderr, "IP\t%s\nIQ\t", pseq);
					fwrite(&seq[t].seq[I.coff[0]], 1, qd, stderr);
					if (pd - qd < opt->min_var_len && qd - pd < opt->min_var_len) {
						score = mg_wfa_cmp(km, l_pseq, pseq, qd, &seq[t].seq[I.coff[0]], 5000, &mlen, &blen);
					} else score = -1, mlen = 0, blen = pd > qd? pd : qd;
					fprintf(stderr, "\nIS\t%d==%d\tnwcmp:%d\tmlen:%d\tblen:%d\n", pd, l_pseq, score, mlen, blen);
					//if (I.voff[0] == 2305301) { for (k = st; k < en; ++k) fprintf(stderr, "%d%c", intv[k].len, "MIDNSHP=XB"[intv[k].op]); fprintf(stderr, "\n"); }
				}
				if (is_inv) { // turn one inversion to two events
					gfa_ins_t I_inv[2];
					I_inv[0].ctg = I_inv[1].ctg = I.ctg;
					// the first event
					I_inv[0].coff[0] = I_inv[0].coff[1] = I.coff[0];
					I_inv[0].v[0] = I.v[0];
					I_inv[0].voff[0] = I.voff[0];
					I_inv[0].v[1] = I.v[1]^1;
					I_inv[0].voff[1] = g->seg[I.v[1]>>1].len - I.voff[1];
					// the second event
					I_inv[1].coff[0] = I_inv[1].coff[1] = I.coff[1];
					I_inv[1].v[0] = I.v[0]^1;
					I_inv[1].voff[0] = g->seg[I.v[0]>>1].len - I.voff[0];
					I_inv[1].v[1] = I.v[1];
					I_inv[1].voff[1] = I.voff[1];
					// insert
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I_inv[0];
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I_inv[1];
					++n_inv;
				} else {
					if (n_ins == m_ins) KEXPAND(km, ins, m_ins);
					ins[n_ins++] = I;
				}
			}
			kfree(0, ss); // this is allocated from malloc() inside mg_mss_all()
			kfree(km, intv);
			kfree(km, sc);
		}
	}
	kfree(km, pseq);
	kfree(km, ovlp);
	if (max_acnt > 0) { // mg_gc_index() allocates nothing when it finds no chain
		kfree(km, soff); kfree(km, qoff);
		kfree(km, sintv); kfree(km, qintv);
	}

	if (n_ins > 0) {
		char **names, **seqs;
		KMALLOC(km, names, n_seq);
		KMALLOC(km, seqs, n_seq);
		for (i = 0; i < n_seq; ++i)
			names[i] = seq[i].name, seqs[i] = seq[i].seq;
		n_ins = gfa_ins_filter(g, n_ins, ins);
		gfa_augment(g, n_ins, ins, n_seq, (const char*const*)names, (const char*const*)seqs);
		kfree(km, ins);
		kfree(km, names);
		kfree(km, seqs);
	}
	if (mg_verbose >= 3 && (opt->flag & MG_G_ENDS))
		fprintf(stderr, "[M::%s::%.3f*%.2f] inserted %d events, including %d inversions and %d end events (%d chains suppressed)\n", __func__,
				realtime() - mg_realtime0, cputime() / (realtime() - mg_realtime0), n_ins, n_inv, n_end, n_sup);
	else if (mg_verbose >= 3)
		fprintf(stderr, "[M::%s::%.3f*%.2f] inserted %d events, including %d inversions\n", __func__,
				realtime() - mg_realtime0, cputime() / (realtime() - mg_realtime0), n_ins, n_inv);
}
