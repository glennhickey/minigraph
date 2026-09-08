#include <string.h>
#include <assert.h>
#include "mgpriv.h"
#include "khashl.h"
#include "kthread.h"
#include "kvec-km.h"
#include "sys.h"

#define idx_hash(a) ((a)>>1)
#define idx_eq(a, b) ((a)>>1 == (b)>>1)
KHASHL_MAP_INIT(KH_LOCAL, idxhash_t, mg_hidx, uint64_t, uint64_t, idx_hash, idx_eq)

typedef struct mg_idx_bucket_s {
	mg128_v a;   // (minimizer, position) array
	int32_t n;   // size of the _p_ array
	uint64_t *p; // position array for minimizers appearing >1 times
	void *h;     // hash table indexing _p_ and minimizers appearing once
} mg_idx_bucket_t;

mg_idx_t *mg_idx_init(int k, int w, int b)
{
	mg_idx_t *gi;
	if (k*2 < b) b = k * 2;
	if (w < 1) w = 1;
	KCALLOC(0, gi, 1);
	gi->w = w, gi->k = k, gi->b = b;
	KCALLOC(0, gi->B, 1<<b);
	return gi;
}

void mg_idx_destroy(mg_idx_t *gi)
{
	uint32_t i;
	if (gi == 0) return;
	if (gi->B) {
		for (i = 0; i < 1U<<gi->b; ++i) {
			free(gi->B[i].p);
			free(gi->B[i].a.a);
			mg_hidx_destroy((idxhash_t*)gi->B[i].h);
		}
		free(gi->B);
	}
	gfa_edseq_destroy(gi->n_seg, gi->es);
	free(gi->occ.a);
	free(gi);
}

/****************
 * Index access *
 ****************/

const uint64_t *mg_idx_hget(const void *h_, const uint64_t *q, int suflen, uint64_t minier, int *n)
{
	khint_t k;
	const idxhash_t *h = (const idxhash_t*)h_;
	*n = 0;
	if (h == 0) return 0;
	k = mg_hidx_get(h, minier>>suflen<<1);
	if (k == kh_end(h)) return 0;
	if (kh_key(h, k)&1) { // special casing when there is only one k-mer
		*n = 1;
		return &kh_val(h, k);
	} else {
		*n = (uint32_t)kh_val(h, k);
		return &q[kh_val(h, k)>>32];
	}
}

const uint64_t *mg_idx_get(const mg_idx_t *gi, uint64_t minier, int *n)
{
	int mask = (1<<gi->b) - 1;
	mg_idx_bucket_t *b = &gi->B[minier&mask];
	return mg_idx_hget(b->h, b->p, gi->b, minier, n);
}

void mg_idx_cal_quantile(const mg_idx_t *gi, int32_t m, float f[], int32_t q[])
{
	int32_t i, c;
	uint64_t n = 0, s;
	for (c = 0; c < gi->occ.n; ++c) n += gi->occ.a[c];
	for (i = 0; i < m; ++i) { // q[i] is the (1-f[i])*n-th smallest occurrence (0-based)
		uint64_t k = (uint64_t)((1.0 - (double)f[i]) * n);
		for (c = 0, s = 0; c + 1 < gi->occ.n; ++c)
			if ((s += gi->occ.a[c]) > k) break;
		q[i] = c;
	}
}

/***************
 * Index build *
 ***************/

void mg_idx_hfree(void *h_)
{
	idxhash_t *h = (idxhash_t*)h_;
	if (h == 0) return;
	mg_hidx_destroy(h);
}

void *mg_idx_a2h(void *km, int32_t n_a, mg128_t *a, int suflen, uint64_t **q_, int32_t *n_)
{
	int32_t N, n, n_keys;
	int32_t j, start_a, start_q;
	idxhash_t *h;
	uint64_t *q;

	*q_ = 0, *n_ = 0;
	if (n_a == 0) return 0;

	// sort by minimizer
	radix_sort_128x(a, a + n_a);

	// count and preallocate
	for (j = 1, n = 1, n_keys = 0, N = 0; j <= n_a; ++j) {
		if (j == n_a || a[j].x>>8 != a[j-1].x>>8) {
			++n_keys;
			if (n > 1) N += n;
			n = 1;
		} else ++n;
	}
	h = mg_hidx_init2(km);
	mg_hidx_resize(h, n_keys);
	KCALLOC(km, q, N);
	*q_ = q, *n_ = N;

	// create the hash table
	for (j = 1, n = 1, start_a = start_q = 0; j <= n_a; ++j) {
		if (j == n_a || a[j].x>>8 != a[j-1].x>>8) {
			khint_t itr;
			int absent;
			mg128_t *p = &a[j-1];
			itr = mg_hidx_put(h, p->x>>8>>suflen<<1, &absent);
			assert(absent && j == start_a + n);
			if (n == 1) {
				kh_key(h, itr) |= 1;
				kh_val(h, itr) = p->y;
			} else {
				int k;
				for (k = 0; k < n; ++k)
					q[start_q + k] = a[start_a + k].y;
				radix_sort_gfa64(&q[start_q], &q[start_q + n]); // sort by position; needed as in-place radix_sort_128x() is not stable
				kh_val(h, itr) = (uint64_t)start_q<<32 | n;
				start_q += n;
			}
			start_a = j, n = 1;
		} else ++n;
	}
	assert(N == start_q);
	return h;
}

typedef struct {
	mg_idx_t *gi;
	int n_threads;
	mg128_v *buf; // n_threads scratch arrays for mg_sketch()
	mg128_v *tb;  // n_threads<<b arrays; thread t appends to tb[t<<b|bucket]
	mg64_v *occ;  // n_threads occurrence histograms
} idx_step_t;

static void worker_sketch(void *data, long i, int tid)
{
	idx_step_t *s = (idx_step_t*)data;
	const gfa_seg_t *seg = &s->gi->g->seg[i];
	mg128_v *a = &s->buf[tid], *tb = &s->tb[(size_t)tid << s->gi->b];
	int mask = (1<<s->gi->b) - 1;
	size_t j;
	a->n = 0;
	mg_sketch(0, seg->seq, seg->len, s->gi->w, s->gi->k, i, a);
	for (j = 0; j < a->n; ++j) {
		mg128_v *p = &tb[a->a[j].x>>8&mask];
		kv_push(mg128_t, 0, *p, a->a[j]);
	}
}

static void worker_post(void *data, long i, int tid)
{
	idx_step_t *s = (idx_step_t*)data;
	mg_idx_bucket_t *b = &s->gi->B[i];
	mg64_v *occ = &s->occ[tid];
	size_t j, n, tot = 0;
	int t;
	for (t = 0; t < s->n_threads; ++t) // gather the pieces of bucket i from all threads
		tot += s->tb[(size_t)t << s->gi->b | i].n;
	if (tot == 0) return;
	if (s->n_threads == 1) {
		b->a = s->tb[i], s->tb[i].a = 0;
	} else {
		KMALLOC(0, b->a.a, tot);
		for (t = 0, b->a.n = 0; t < s->n_threads; ++t) {
			mg128_v *p = &s->tb[(size_t)t << s->gi->b | i];
			if (p->n > 0) memcpy(&b->a.a[b->a.n], p->a, p->n * sizeof(mg128_t));
			b->a.n += p->n;
			kfree(0, p->a);
			p->a = 0;
		}
	}
	b->h = (idxhash_t*)mg_idx_a2h(0, b->a.n, b->a.a, s->gi->b, &b->p, &b->n);
	for (j = 1, n = 1; j <= b->a.n; ++j) { // b->a is sorted by minimizer now; count occurrences
		if (j < b->a.n && b->a.a[j].x>>8 == b->a.a[j-1].x>>8) {
			++n;
			continue;
		}
		if (n >= occ->n) {
			int32_t m = occ->n;
			occ->n = n + 1;
			kroundup32(occ->n);
			KREALLOC(0, occ->a, occ->n);
			memset(&occ->a[m], 0, (occ->n - m) * sizeof(uint64_t));
		}
		++occ->a[n];
		n = 1;
	}
	kfree(0, b->a.a);
	b->a.n = b->a.m = 0, b->a.a = 0;
}

int mg_gfa_overlap(const gfa_t *g)
{
	int64_t i;
	for (i = 0; i < g->n_arc; ++i) // non-zero overlap
		if (g->arc[i].ov != 0 || g->arc[i].ow != 0)
			return 1;
	return 0;
}

mg_idx_t *mg_index_core(gfa_t *g, int k, int w, int b, int n_threads)
{
	mg_idx_t *gi;
	idx_step_t s;
	int i, j;

	if (mg_gfa_overlap(g)) {
		if (mg_verbose >= 1)
			fprintf(stderr, "[E::%s] minigraph doesn't work with graphs containing overlapping segments\n", __func__);
		return 0;
	}
	gi = mg_idx_init(k, w, b);
	gi->g = g;

	if (n_threads < 1) n_threads = 1;
	s.gi = gi, s.n_threads = n_threads;
	KCALLOC(0, s.buf, n_threads);
	KCALLOC(0, s.tb, (size_t)n_threads << gi->b);
	KCALLOC(0, s.occ, n_threads);
	kt_for(n_threads, worker_sketch, &s, g->n_seg);
	for (i = 0; i < n_threads; ++i) free(s.buf[i].a);
	free(s.buf);
	kt_for(n_threads, worker_post, &s, 1<<gi->b);
	free(s.tb);
	for (i = 0; i < n_threads; ++i) // merge the per-thread histograms
		if (gi->occ.n < s.occ[i].n) gi->occ.n = s.occ[i].n;
	KCALLOC(0, gi->occ.a, gi->occ.n);
	for (i = 0; i < n_threads; ++i) {
		for (j = 0; j < s.occ[i].n; ++j) gi->occ.a[j] += s.occ[i].a[j];
		free(s.occ[i].a);
	}
	free(s.occ);
	return gi;
}

static void worker_upper(void *data, long i, int tid)
{
	gfa_seg_t *s = &((gfa_t*)data)->seg[i];
	int32_t j;
	for (j = 0; j < s->len; ++j)
		if (s->seq[j] >= 'a' && s->seq[j] <= 'z')
			s->seq[j] -= 32;
}

mg_idx_t *mg_index(gfa_t *g, const mg_idxopt_t *io, int n_threads, mg_mapopt_t *mo)
{
	mg_idx_t *gi;
	if (!g->is_upper) { // gfa_augment() only adds uppercase sequences, so this is needed once
		kt_for(n_threads, worker_upper, g, g->n_seg);
		g->is_upper = 1;
	}
	gi = mg_index_core(g, io->k, io->w, io->bucket_bits, n_threads);
	if (gi == 0) return 0;
	gi->es = gfa_edseq_init(gi->g, n_threads);
	gi->n_seg = g->n_seg;
	if (mg_verbose >= 3)
		fprintf(stderr, "[M::%s::%.3f*%.2f] indexed the graph\n", __func__,
				realtime() - mg_realtime0, cputime() / (realtime() - mg_realtime0));
	if (mo) mg_opt_update(gi, mo, 0);
	return gi;
}
