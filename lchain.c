#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include "mgpriv.h"
#include "kalloc.h"
#include "krmq.h"
#include "kthread.h"
#include "kavl.h"

static int64_t mg_chain_bk_end(int32_t max_drop, const mg128_t *z, const int32_t *f, const int64_t *p, int32_t *t, int64_t k)
{
	int64_t i = z[k].y, end_i = -1, max_i = i;
	int32_t max_s = 0;
	if (i < 0 || t[i] != 0) return i;
	do {
		int32_t s;
		t[i] = 2;
		end_i = i = p[i];
		s = i < 0? z[k].x : (int32_t)z[k].x - f[i];
		if (s > max_s) max_s = s, max_i = i;
		else if (max_s - s > max_drop) break;
	} while (i >= 0 && t[i] == 0);
	for (i = z[k].y; i >= 0 && i != end_i; i = p[i]) // reset modified t[]
		t[i] = 0;
	return max_i;
}

uint64_t *mg_chain_backtrack(void *km, int64_t n, const int32_t *f, const int64_t *p, int32_t *v, int32_t *t, int32_t min_cnt, int32_t min_sc, int32_t max_drop,
							 int32_t extra_u, int32_t *n_u_, int32_t *n_v_)
{
	mg128_t *z;
	uint64_t *u;
	int64_t i, k, n_z, n_v;
	int32_t n_u;

	*n_u_ = *n_v_ = 0;
	for (i = 0, n_z = 0; i < n; ++i) // precompute n_z
		if (f[i] >= min_sc) ++n_z;
	if (n_z == 0) return 0;
	KMALLOC(km, z, n_z);
	for (i = 0, k = 0; i < n; ++i) // populate z[]
		if (f[i] >= min_sc) z[k].x = f[i], z[k++].y = i;
	radix_sort_128x(z, z + n_z);

	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // precompute n_u
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				++n_v, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				++n_u;
			else n_v = n_v0;
		}
	}
	KMALLOC(km, u, n_u + extra_u);
	memset(t, 0, n * 4);
	for (k = n_z - 1, n_v = n_u = 0; k >= 0; --k) { // populate u[]
		if (t[z[k].y] == 0) {
			int64_t n_v0 = n_v, end_i;
			int32_t sc;
			end_i = mg_chain_bk_end(max_drop, z, f, p, t, k);
			for (i = z[k].y; i != end_i; i = p[i])
				v[n_v++] = i, t[i] = 1;
			sc = i < 0? z[k].x : (int32_t)z[k].x - f[i];
			if (sc >= min_sc && n_v > n_v0 && n_v - n_v0 >= min_cnt)
				u[n_u++] = (uint64_t)sc << 32 | (n_v - n_v0);
			else n_v = n_v0;
		}
	}
	kfree(km, z);
	assert(n_v < INT32_MAX);
	*n_u_ = n_u, *n_v_ = n_v;
	return u;
}

static mg128_t *compact_a(void *km, int32_t n_u, uint64_t *u, int32_t n_v, int32_t *v, mg128_t *a)
{
	mg128_t *b, *w;
	uint64_t *u2;
	int64_t i, j, k;

	// write the result to b[]
	KMALLOC(km, b, n_v);
	for (i = 0, k = 0; i < n_u; ++i) {
		int32_t k0 = k, ni = (int32_t)u[i];
		for (j = 0; j < ni; ++j)
			b[k++] = a[v[k0 + (ni - j - 1)]];
	}
	kfree(km, v);

	// sort u[] and a[] by the target position, such that adjacent chains may be joined
	KMALLOC(km, w, n_u);
	for (i = k = 0; i < n_u; ++i) {
		w[i].x = b[k].x, w[i].y = (uint64_t)k<<32|i;
		k += (int32_t)u[i];
	}
	radix_sort_128x(w, w + n_u);
	KMALLOC(km, u2, n_u);
	for (i = k = 0; i < n_u; ++i) {
		int32_t j = (int32_t)w[i].y, n = (int32_t)u[j];
		u2[i] = u[j];
		memcpy(&a[k], &b[w[i].y>>32], n * sizeof(mg128_t));
		k += n;
	}
	memcpy(u, u2, n_u * 8);
	memcpy(b, a, k * sizeof(mg128_t)); // write _a_ to _b_ and deallocate _a_ because _a_ is oversized, sometimes a lot
	kfree(km, a); kfree(km, w); kfree(km, u2);
	return b;
}

static inline int32_t comput_sc(const mg128_t *ai, const mg128_t *aj, int32_t max_dist_x, int32_t max_dist_y, int32_t bw, float chn_pen_gap, float chn_pen_skip, int is_cdna, int n_seg)
{
	int32_t dq = (int32_t)ai->y - (int32_t)aj->y, dr, dd, dg, q_span, sc;
	int32_t sidi = (ai->y & MG_SEED_SEG_MASK) >> MG_SEED_SEG_SHIFT;
	int32_t sidj = (aj->y & MG_SEED_SEG_MASK) >> MG_SEED_SEG_SHIFT;
	if (dq <= 0 || dq > max_dist_x) return INT32_MIN;
	dr = (int32_t)(ai->x - aj->x);
	if (sidi == sidj && (dr == 0 || dq > max_dist_y)) return INT32_MIN;
	dd = dr > dq? dr - dq : dq - dr;
	if (sidi == sidj && dd > bw) return INT32_MIN;
	if (n_seg > 1 && !is_cdna && sidi == sidj && dr > max_dist_y) return INT32_MIN;
	dg = dr < dq? dr : dq;
	q_span = aj->y>>32&0xff;
	sc = q_span < dg? q_span : dg;
	if (dd || dg > q_span) {
		float lin_pen, log_pen;
		lin_pen = chn_pen_gap * (float)dd + chn_pen_skip * (float)dg;
		log_pen = dd >= 1? mg_log2(dd + 1) : 0.0f; // mg_log2() only works for dd>=2
		if (is_cdna || sidi != sidj) {
			if (sidi != sidj && dr == 0) ++sc; // possibly due to overlapping paired ends; give a minor bonus
			else if (dr > dq || sidi != sidj) sc -= (int)(lin_pen < log_pen? lin_pen : log_pen); // deletion or jump between paired ends
			else sc -= (int)(lin_pen + .5f * log_pen);
		} else sc -= (int)(lin_pen + .5f * log_pen);
	}
	return sc;
}

/* Input:
 *   a[].x: tid<<33 | rev<<32 | tpos
 *   a[].y: flags<<40 | q_span<<32 | q_pos
 * Output:
 *   n_u: #chains
 *   u[]: score<<32 | #anchors (sum of lower 32 bits of u[] is the returned length of a[])
 * input a[] is deallocated on return
 */
mg128_t *mg_lchain_dp(int max_dist_x, int max_dist_y, int bw, int max_skip, int max_iter, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					  int is_cdna, int n_seg, int64_t n, mg128_t *a, int *n_u_, uint64_t **_u, void *km)
{ // TODO: make sure this works when n has more than 32 bits
	int32_t *f, *t, *v, n_u, n_v, mmax_f = 0, max_drop = bw;
	int64_t *p, i, j, max_ii, st = 0, n_iter = 0;
	uint64_t *u;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist_x < bw) max_dist_x = bw;
	if (max_dist_y < bw && !is_cdna) max_dist_y = bw;
	if (is_cdna) max_drop = INT32_MAX;
	KMALLOC(km, p, n);
	KMALLOC(km, f, n);
	KMALLOC(km, v, n);
	KCALLOC(km, t, n);

	// fill the score and backtrack arrays
	for (i = 0, max_ii = -1; i < n; ++i) {
		int64_t max_j = -1, end_j;
		int32_t max_f = a[i].y>>32&0xff, n_skip = 0;
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist_x)) ++st;
		if (i - st > max_iter) st = i - max_iter;
		for (j = i - 1; j >= st; --j) {
			int32_t sc;
			sc = comput_sc(&a[i], &a[j], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			++n_iter;
			if (sc == INT32_MIN) continue;
			sc += f[j];
			if (sc > max_f) {
				max_f = sc, max_j = j;
				if (n_skip > 0) --n_skip;
			} else if (t[j] == (int32_t)i) {
				if (++n_skip > max_skip)
					break;
			}
			if (p[j] >= 0) t[p[j]] = i;
		}
		end_j = j;
		if (max_ii < 0 || a[i].x - a[max_ii].x > (int64_t)max_dist_x) {
			int32_t max = INT32_MIN;
			max_ii = -1;
			for (j = i - 1; j >= st; --j)
				if (max < f[j]) max = f[j], max_ii = j;
		}
		if (max_ii >= 0 && max_ii < end_j) {
			int32_t tmp;
			tmp = comput_sc(&a[i], &a[max_ii], max_dist_x, max_dist_y, bw, chn_pen_gap, chn_pen_skip, is_cdna, n_seg);
			if (tmp != INT32_MIN && max_f < tmp + f[max_ii])
				max_f = tmp + f[max_ii], max_j = max_ii;
		}
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (max_ii < 0 || (a[i].x - a[max_ii].x <= (int64_t)max_dist_x && f[max_ii] < f[i]))
			max_ii = i;
		if (mmax_f < max_f) mmax_f = max_f;
	}
	if (mg_dbg_flag & MG_DBG_LC_PROF) fprintf(stderr, "LP\tn_iter=%ld\tmmax_f=%d\n", (long)n_iter, mmax_f);

	u = mg_chain_backtrack(km, n, f, p, v, t, min_cnt, min_sc, max_drop, 0, &n_u, &n_v);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}

typedef struct lc_elem_s {
	int32_t y;
	int64_t i;
	double pri;
	KRMQ_HEAD(struct lc_elem_s) head;
} lc_elem_t;

#define lc_elem_cmp(a, b) ((a)->y < (b)->y? -1 : (a)->y > (b)->y? 1 : ((a)->i > (b)->i) - ((a)->i < (b)->i))
#define lc_elem_lt2(a, b) ((a)->pri < (b)->pri)
KRMQ_INIT(lc_elem, lc_elem_t, head, lc_elem_cmp, lc_elem_lt2)

KALLOC_POOL_INIT(rmq, lc_elem_t)

typedef struct lc_inode_s { // node of the inner tree; only the (y,i) order is needed, not RMQ
	int32_t y, i;
	KAVL_HEAD(struct lc_inode_s) head;
} lc_inode_t;

#define lc_inode_cmp(a, b) ((a)->y < (b)->y? -1 : (a)->y > (b)->y? 1 : ((a)->i > (b)->i) - ((a)->i < (b)->i))
KAVL_INIT(lc_in, lc_inode_t, head, lc_inode_cmp)

KALLOC_POOL_INIT(lcin, lc_inode_t)

static inline int32_t comput_sc_simple(const mg128_t *ai, const mg128_t *aj, float chn_pen_gap, float chn_pen_skip, int32_t *exact, int32_t *width)
{
	int32_t dq = (int32_t)ai->y - (int32_t)aj->y, dr, dd, dg, q_span, sc;
	dr = (int32_t)(ai->x - aj->x);
	*width = dd = dr > dq? dr - dq : dq - dr;
	dg = dr < dq? dr : dq;
	q_span = aj->y>>32&0xff;
	sc = q_span < dg? q_span : dg;
	if (exact) *exact = (dd == 0 && dg <= q_span);
	if (dd || dq > q_span) {
		float lin_pen, log_pen;
		lin_pen = chn_pen_gap * (float)dd + chn_pen_skip * (float)dg;
		log_pen = dd >= 1? mg_log2(dd + 1) : 0.0f; // mg_log2() only works for dd>=2
		sc -= (int)(lin_pen + .5f * log_pen);
	}
	return sc;
}

/*****************************************************************************
 * RMQ linear chaining, parallelized over (segment,strand) anchor groups
 *
 * The fill loop below is the original serial loop of mg_lchain_rmq(), moved
 * into lc_rmq_fill() so that it can be applied to a sub-range of a[].
 *
 * Independence argument (see also the comment on mg_lchain_rmq()): a[] is
 * processed as a sequence of maximal runs ("groups") of equal a[].x>>32
 * (= segment<<1 | strand).  At the first anchor i of a run, every anchor
 * j < i has a different a[].x>>32, so the two eviction loops advance st and
 * st_inner all the way to i and erase every node from both trees; the "add
 * in-range anchors" block above them has already set i0 = i (a[i0].x != a[i].x
 * always holds across a run boundary), and the nodes it inserted for the
 * previous run are erased by those same eviction loops before any query is
 * made.  So at a run boundary the state carried by the loop is exactly
 * (root = 0, root_inner = 0, st = st_inner = i0 = i) - which is what
 * lc_rmq_fill() starts from - and n_iter/mmax_f/max_rmq_size are pure
 * bookkeeping.  Within a run, f/p/v/t are read and written only at indices
 * of that run (all j come from the trees, and p[] never points out of the
 * run), and a[] is not modified.  Therefore the runs can be processed in any
 * order, on any thread, and the resulting f/p/v/t are bit-identical to the
 * serial loop.  mg_chain_backtrack() then runs globally as before.
 *****************************************************************************/

typedef struct { // per-thread scratch; padded to a cache line, as threads write to adjacent entries
	void *km;      // private arena backing the two node pools
	kmp_rmq_t *mp;
	kmp_lcin_t *mpi;
	int64_t n_iter;
	int64_t mp_max;
	int32_t mmax_f, max_rmq_size;
	int64_t pad[2];
} lc_buf_t;

typedef struct {
	const mg128_t *a;
	int64_t n;
	int32_t *f, *t, *v;
	int64_t *p;
	int32_t max_dist, max_dist_inner, bw, max_chn_skip, cap_rmq_size;
	float chn_pen_gap, chn_pen_skip;
	const int64_t *bnd;  // group g spans anchors [bnd[g], bnd[g+1])
	const uint64_t *ord; // group ids as size<<32|id, largest group first
	lc_buf_t *buf;
} lc_par_t;

// fill f[]/p[]/v[] for anchors [st_g, en_g); the range must start at a group boundary and end at one
static void lc_rmq_fill(const lc_par_t *ap, int64_t st_g, int64_t en_g, lc_buf_t *w, int flush)
{
	const mg128_t *a = ap->a;
	const int64_t n = ap->n;
	int32_t *f = ap->f, *t = ap->t, *v = ap->v;
	int64_t *p = ap->p;
	const int32_t max_dist = ap->max_dist, max_dist_inner = ap->max_dist_inner, bw = ap->bw;
	const int32_t max_chn_skip = ap->max_chn_skip, cap_rmq_size = ap->cap_rmq_size;
	const float chn_pen_gap = ap->chn_pen_gap, chn_pen_skip = ap->chn_pen_skip;
	kmp_rmq_t *mp = w->mp;
	kmp_lcin_t *mpi = w->mpi;
	lc_elem_t *root = 0;
	lc_inode_t *root_inner = 0;
	int64_t i, i0, st = st_g, st_inner = st_g, n_iter = 0; // accumulate the stats in locals: w is shared between threads
	int32_t mmax_f = 0, max_rmq_size = 0;

	for (i = i0 = st_g; i < en_g; ++i) {
		int64_t max_j = -1;
		int32_t q_span = a[i].y>>32&0xff, max_f = q_span;
		lc_elem_t s, *q, lo, hi;
		// add in-range anchors
		if (i0 < i && a[i0].x != a[i].x) {
			int64_t j;
			for (j = i0; j < i; ++j) {
				q = kmp_alloc_rmq(mp);
				q->y = (int32_t)a[j].y, q->i = j, q->pri = -(f[j] + 0.5 * chn_pen_gap * ((int32_t)a[j].x + (int32_t)a[j].y));
				krmq_insert(lc_elem, &root, q, 0);
				if (max_dist_inner > 0) {
					lc_inode_t *r = kmp_alloc_lcin(mpi);
					r->y = q->y, r->i = j;
					kavl_insert(lc_in, &root_inner, r, 0);
				}
			}
			i0 = i;
		}
		// get rid of active chains out of range
		while (st < i && (a[i].x>>32 != a[st].x>>32 || a[i].x > a[st].x + max_dist || krmq_size(head, root) > cap_rmq_size)) {
			s.y = (int32_t)a[st].y, s.i = st;
			if (root && (q = krmq_erase(lc_elem, &root, &s, 0)) != 0) // krmq_erase() searches for s itself
				kmp_free_rmq(mp, q);
			++st;
		}
		if (max_dist_inner > 0)  { // similar to the block above, but applied to the inner tree
			while (st_inner < i && (a[i].x>>32 != a[st_inner].x>>32 || a[i].x > a[st_inner].x + max_dist_inner || kavl_size(head, root_inner) > cap_rmq_size)) {
				lc_inode_t s, *q;
				s.y = (int32_t)a[st_inner].y, s.i = st_inner;
				if (root_inner && (q = kavl_erase(lc_in, &root_inner, &s, 0)) != 0)
					kmp_free_lcin(mpi, q);
				++st_inner;
			}
		}
		// RMQ
		lo.i = INT32_MAX, lo.y = (int32_t)a[i].y - max_dist;
		hi.i = 0, hi.y = (int32_t)a[i].y - 1;
		if ((q = krmq_rmq(lc_elem, root, &lo, &hi)) != 0) {
			int32_t sc, exact, width, n_skip = 0;
			int64_t j = q->i;
			assert(q->y >= lo.y && q->y <= hi.y);
			sc = f[j] + comput_sc_simple(&a[i], &a[j], chn_pen_gap, chn_pen_skip, &exact, &width);
			if (width <= bw && sc > max_f) max_f = sc, max_j = j;
			if (!exact && root_inner && (int32_t)a[i].y > 0) {
				lc_inode_t s;
				const lc_inode_t *q;
				int32_t width, n_rmq_iter = 0;
				kavl_itr_t(lc_in) itr;
				s.y = (int32_t)a[i].y - 1, s.i = n;
				kavl_itr_find(lc_in, root_inner, &s, &itr); // the iterator stops at the last node on the search path
				q = kavl_at(&itr);
				if (q && lc_inode_cmp(&s, q) < 0) // this node is larger than s; move to the largest node smaller than s
					q = kavl_itr_prev(lc_in, &itr)? kavl_at(&itr) : 0;
				while (q) {
					if (q->y < (int32_t)a[i].y - max_dist_inner) break;
					++n_rmq_iter;
					j = q->i;
					sc = f[j] + comput_sc_simple(&a[i], &a[j], chn_pen_gap, chn_pen_skip, 0, &width);
					if (width <= bw) {
						if (sc > max_f) {
							max_f = sc, max_j = j;
							if (n_skip > 0) --n_skip;
						} else if (t[j] == (int32_t)i) {
							if (++n_skip > max_chn_skip)
								break;
						}
						if (p[j] >= 0) t[p[j]] = i;
					}
					if (!kavl_itr_prev(lc_in, &itr)) break;
					q = kavl_at(&itr);
				}
				n_iter += n_rmq_iter;
			}
		}
		// set max
		assert(max_j < 0 || (a[max_j].x < a[i].x && (int32_t)a[max_j].y < (int32_t)a[i].y));
		f[i] = max_f, p[i] = max_j;
		v[i] = max_j >= 0 && v[max_j] > max_f? v[max_j] : max_f; // v[] keeps the peak score up to i; f[] is the score ending at i, not always the peak
		if (mmax_f < max_f) mmax_f = max_f;
		if (max_rmq_size < (int32_t)krmq_size(head, root)) max_rmq_size = krmq_size(head, root);
	}
	w->n_iter += n_iter;
	if (w->mmax_f < mmax_f) w->mmax_f = mmax_f;
	if (w->max_rmq_size < max_rmq_size) w->max_rmq_size = max_rmq_size;
	if (flush) { // give the nodes left in the trees back to the pools, for the next group on this thread
		if (root) {
			krmq_itr_t(lc_elem) itr;
			const lc_elem_t *q;
			krmq_itr_first(lc_elem, root, &itr);
			while ((q = krmq_at(&itr)) != 0) { // kmp_free_*() only pushes the pointer, it doesn't touch the node
				kmp_free_rmq(mp, (lc_elem_t*)q);
				if (!krmq_itr_next(lc_elem, &itr)) break;
			}
		}
		if (root_inner) {
			kavl_itr_t(lc_in) itr;
			const lc_inode_t *q;
			kavl_itr_first(lc_in, root_inner, &itr);
			while ((q = kavl_at(&itr)) != 0) {
				kmp_free_lcin(mpi, (lc_inode_t*)q);
				if (!kavl_itr_next(lc_in, &itr)) break;
			}
		}
	}
}

static void lc_worker(void *data, long k, int tid) // kt_for() callback: one group per call
{
	lc_par_t *ap = (lc_par_t*)data;
	lc_buf_t *w = &ap->buf[tid];
	int64_t g = (int64_t)(uint32_t)ap->ord[k];
	if (w->km == 0) { // NB: km_init2(0,...) is backed by malloc, so this doesn't touch the shared kalloc arena
		w->km = km_init2(0, 0x10000);
		w->mp = kmp_init_rmq(w->km);
		if (ap->max_dist_inner > 0) w->mpi = kmp_init_lcin(w->km);
	}
	lc_rmq_fill(ap, ap->bnd[g], ap->bnd[g + 1], w, 1);
}

static void lc_buf_reduce(lc_buf_t *dst, const lc_buf_t *src)
{
	dst->n_iter += src->n_iter;
	if (dst->mmax_f < src->mmax_f) dst->mmax_f = src->mmax_f;
	if (dst->max_rmq_size < src->max_rmq_size) dst->max_rmq_size = src->max_rmq_size;
	if (dst->mp_max < src->mp_max) dst->mp_max = src->mp_max;
}

/* Input:
 *   a[].x: tid<<33 | rev<<32 | tpos  (sorted)
 *   a[].y: flags<<40 | q_span<<32 | q_pos
 * The DP is independent within each maximal run of equal a[].x>>32; with
 * n_threads > 1 the runs are chained in parallel (largest first).  The result
 * does not depend on n_threads.
 */
mg128_t *mg_lchain_rmq(int max_dist, int max_dist_inner, int bw, int max_chn_skip, int cap_rmq_size, int min_cnt, int min_sc, float chn_pen_gap, float chn_pen_skip,
					   int64_t n, mg128_t *a, int *n_u_, uint64_t **_u, void *km, int n_threads)
{
	int32_t *f, *t, *v, n_u, n_v, max_drop = bw;
	int64_t *p, n_grp = 0;
	int64_t *bnd = 0;
	uint64_t *u, *ord = 0;
	lc_par_t ap;
	lc_buf_t red;
	int par, nt_used = 1;

	if (_u) *_u = 0, *n_u_ = 0;
	if (n == 0 || a == 0) {
		kfree(km, a);
		return 0;
	}
	if (max_dist < bw) max_dist = bw;
	if (max_dist_inner <= 0 || max_dist_inner >= max_dist) max_dist_inner = 0;
	KMALLOC(km, p, n);
	KMALLOC(km, f, n);
	KCALLOC(km, t, n);
	KMALLOC(km, v, n);

	memset(&ap, 0, sizeof(lc_par_t));
	memset(&red, 0, sizeof(lc_buf_t));
	ap.a = a, ap.n = n, ap.f = f, ap.t = t, ap.v = v, ap.p = p;
	ap.max_dist = max_dist, ap.max_dist_inner = max_dist_inner, ap.bw = bw;
	ap.max_chn_skip = max_chn_skip, ap.cap_rmq_size = cap_rmq_size;
	ap.chn_pen_gap = chn_pen_gap, ap.chn_pen_skip = chn_pen_skip;

	par = (n_threads > 1); // the caller decides whether the query is worth threading; see mg_lc_threads()
	if (par || (mg_dbg_flag & MG_DBG_LC_PROF)) { // find the group boundaries in one pass
		int64_t i, m_grp = 0;
		for (i = 0; i < n; ++i)
			if (i == 0 || a[i].x>>32 != a[i-1].x>>32) {
				if (n_grp + 1 >= m_grp) KEXPAND(km, bnd, m_grp);
				bnd[n_grp++] = i;
			}
		bnd[n_grp] = n;
	}

	if (par && n_grp > 1) { // chain the groups in parallel
		int64_t i;
		int j, nt = n_threads < n_grp? n_threads : (int)n_grp;
		KMALLOC(km, ord, n_grp);
		for (i = 0; i < n_grp; ++i)
			ord[i] = (uint64_t)(bnd[i+1] - bnd[i]) << 32 | (uint64_t)i;
		radix_sort_gfa64(ord, ord + n_grp);
		for (i = 0; i < n_grp>>1; ++i) { // largest group first, for load balance
			uint64_t tmp = ord[i];
			ord[i] = ord[n_grp - 1 - i], ord[n_grp - 1 - i] = tmp;
		}
		KCALLOC(km, ap.buf, nt);
		ap.bnd = bnd, ap.ord = ord;
		nt_used = nt;
		kt_for(nt, lc_worker, &ap, n_grp);
		for (j = 0; j < nt; ++j) {
			if (ap.buf[j].km == 0) continue;
			ap.buf[j].mp_max = ap.buf[j].mp->max;
			lc_buf_reduce(&red, &ap.buf[j]);
			km_destroy(ap.buf[j].km); // frees both pools
		}
		kfree(km, ap.buf);
	} else { // serial: the whole array is one range, which is exactly the original loop
		red.km = km_init2(km, 0x10000);
		red.mp = kmp_init_rmq(red.km);
		if (max_dist_inner > 0) red.mpi = kmp_init_lcin(red.km);
		lc_rmq_fill(&ap, 0, n, &red, 0);
		red.mp_max = red.mp->max;
		km_destroy(red.km);
	}
	if (mg_dbg_flag & MG_DBG_LC_PROF) {
		int64_t i;
		uint64_t h = 0x1234567890abcdefULL;
		for (i = 0; i < n; ++i) // checksum of the DP result; must not depend on n_threads
			h = (h ^ ((uint64_t)(uint32_t)f[i] << 32 | (uint32_t)v[i])) * 0x100000001b3ULL, h ^= (uint64_t)(p[i] + 1) + (h >> 29);
		fprintf(stderr, "LP\tn_iter=%ld\tmmax_f=%d\trmq_size=%d\tmp_max=%ld\tn_grp=%ld\tnt=%d\tfpv=%016lx\n", (long)red.n_iter, red.mmax_f, red.max_rmq_size,
				(long)red.mp_max, (long)n_grp, nt_used, (unsigned long)h);
		if (n_grp > 0) { // group-size distribution and the speedup it allows, plus the 8 largest groups
			int64_t i, j, top[8], n_top = n_grp < 8? n_grp : 8;
			double sum_mlogm = 0.0;
			for (j = 0; j < 8; ++j) top[j] = 0;
			for (i = 0; i < n_grp; ++i) { // partial selection sort of the 8 largest
				int64_t sz = bnd[i+1] - bnd[i];
				sum_mlogm += (double)sz * mg_log2(sz + 1.0);
				for (j = 0; j < n_top; ++j)
					if (sz > top[j]) { int64_t tmp = top[j]; top[j] = sz, sz = tmp; }
			}
			// the largest group is one task, so the speedup is at most (total work)/(work of the largest group)
			fprintf(stderr, "LG\tn=%ld\tn_grp=%ld\tbound_lin=%.2f\tbound_mlogm=%.2f", (long)n, (long)n_grp,
					(double)n / top[0], sum_mlogm / ((double)top[0] * mg_log2(top[0] + 1.0)));
			for (j = 0; j < n_top; ++j) fprintf(stderr, "\t%ld", (long)top[j]);
			fprintf(stderr, "\n");
		}
	}
	kfree(km, ord); kfree(km, bnd);

	u = mg_chain_backtrack(km, n, f, p, v, t, min_cnt, min_sc, max_drop, 0, &n_u, &n_v);
	*n_u_ = n_u, *_u = u; // NB: note that u[] may not be sorted by score here
	kfree(km, p); kfree(km, f); kfree(km, t);
	if (n_u == 0) {
		kfree(km, a); kfree(km, v);
		return 0;
	}
	return compact_a(km, n_u, u, n_v, v, a);
}

mg_lchain_t *mg_lchain_gen(void *km, uint32_t hash, int qlen, int n_u, uint64_t *u, mg128_t *a)
{
	mg128_t *z;
	mg_lchain_t *r;
	int i, k;

	if (n_u == 0) return 0;
	KCALLOC(km, r, n_u);

	// sort by query position
	KMALLOC(km, z, n_u);
	for (i = k = 0; i < n_u; ++i) {
		int32_t qs = (int32_t)a[k].y + 1 - (a[k].y>>32 & 0xff);
		z[i].x = (uint64_t)qs << 32 | u[i] >> 32;
		z[i].y = (uint64_t)k << 32 | (int32_t)u[i];
		k += (int32_t)u[i];
	}
	radix_sort_128x(z, z + n_u);

	// populate r[]
	for (i = 0; i < n_u; ++i) {
		mg_lchain_t *ri = &r[i];
		int32_t k = z[i].y >> 32, q_span = a[k].y >> 32 & 0xff;
		ri->off = k;
		ri->cnt = (int32_t)z[i].y;
		ri->score = (uint32_t)z[i].x;
		ri->v = a[k].x >> 32;
		ri->rs = (int32_t)a[k].x + 1 > q_span? (int32_t)a[k].x + 1 - q_span : 0; // for HPC k-mer
		ri->qs = z[i].x >> 32;
		ri->re = (int32_t)a[k + ri->cnt - 1].x + 1;
		ri->qe = (int32_t)a[k + ri->cnt - 1].y + 1;
	}
	kfree(km, z);
	return r;
}

static int32_t get_mini_idx(const mg128_t *a, int32_t n, const int32_t *mini_pos)
{
	int32_t x, L = 0, R = n - 1;
	x = (int32_t)a->y;
	while (L <= R) { // binary search
		int32_t m = ((uint64_t)L + R) >> 1;
		int32_t y = mini_pos[m];
		if (y < x) L = m + 1;
		else if (y > x) R = m - 1;
		else return m;
	}
	return -1;
}

/* Before:
 *   a[].x: tid<<33 | rev<<32 | tpos
 *   a[].y: flags<<40 | q_span<<32 | q_pos
 * After:
 *   a[].x: mini_pos<<32 | tpos
 *   a[].y: same
 */
void mg_update_anchors(int32_t n_a, mg128_t *a, int32_t n, const int32_t *mini_pos)
{
	int32_t st, j, k;
	if (n_a <= 0) return;
	st = get_mini_idx(&a[0], n, mini_pos);
	assert(st >= 0);
	for (k = 0, j = st; j < n && k < n_a; ++j)
		if ((int32_t)a[k].y == mini_pos[j])
			a[k].x = (uint64_t)j << 32 | (a[k].x & 0xffffffffU), ++k;
	assert(k == n_a);
}
