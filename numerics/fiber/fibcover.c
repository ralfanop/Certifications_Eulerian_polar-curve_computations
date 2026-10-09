/* fibcover.c -- certificate of the dual fiber inequality on a band of prices c:
 *
 *     J(c, a) <= d(c) = (3 nu / 2)(sqrt(1 + c^2) - c)     for every unit a in R^4 and every c in [cmin, cmax].
 *
 * Method (independent of the authors' envelope/panel method):
 *  - S^3 modulo a -> -a (J(c,-a) = J(c,a)) is covered by the radial projections of the four facets {x_f = +1} of the
 *    cube [-1,1]^4; a patch is the projection of a dyadic sub-cube of a facet.
 *  - If v_1..v_8 are the normalized corners of a patch and n its normalized centre, every unit a in the patch is
 *    a = t q with q in conv(v_j) and 1 <= t <= T := 1 / min_j <v_j, n>.  J is homogeneous, J(c, t q) = t J(c/t, q),
 *    nonincreasing in c, and convex in the coefficient vector.  Hence for c in [cL, cU]
 *         J(c, a) <= T * max_j J(cL / T, v_j),
 *    and d(c) >= d(cU).  A (patch, band) pair is certified when T max_j J(cL/T, v_j) < d(cU), all in ball arithmetic
 *    with the exact closed-form enclosure of J from fibcore.h.
 *  - Uncertified pairs are split (patch bisection or band bisection), best-first by nothing: plain DFS stack.
 *
 * usage: fibcover cmin cmax nbands [maxitems]
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "fibcore.h"

typedef struct { int f; double l[3], h[3]; double cL, cU; } item_t;
static slong PREC = 128;

static void corner_vec(arb_ptr v, int f, const double *x)   /* x: 3 free coordinates; v normalized */
{
    arb_t n; arb_init(n); int k = 0;
    for (int i = 0; i < 4; i++) { if (i == f) arb_one(v + i); else arb_set_d(v + i, x[k++]); }
    arb_zero(n); for (int i = 0; i < 4; i++) arb_addmul(n, v + i, v + i, PREC);
    arb_rsqrt(n, n, PREC); for (int i = 0; i < 4; i++) arb_mul(v + i, v + i, n, PREC);
    arb_clear(n);
}

static double ub(const arb_t x) { arf_t u; arf_init(u); arb_get_ubound_arf(u, x, 60); double r = arf_get_d(u, ARF_RND_UP); arf_clear(u); return r; }
static double lb(const arb_t x) { arf_t u; arf_init(u); arb_get_lbound_arf(u, x, 60); double r = arf_get_d(u, ARF_RND_DOWN); arf_clear(u); return r; }

/* returns 1 certified, 0 not, -1 evaluation failure; *M, *dU, *Jc filled (doubles, rounded outward) */
static int test_item(const item_t *it, double *Mo, double *dUo, double *Jco)
{
    arb_struct V[8][4], N[4]; arb_t t, T, cp, J, d, M; double xc[3];
    for (int j = 0; j < 8; j++) for (int i = 0; i < 4; i++) arb_init(&V[j][i]);
    for (int i = 0; i < 4; i++) arb_init(N + i);
    arb_init(t); arb_init(T); arb_init(cp); arb_init(J); arb_init(d); arb_init(M);
    for (int k = 0; k < 3; k++) xc[k] = 0.5 * (it->l[k] + it->h[k]);     /* exact (dyadic) */
    corner_vec(N, it->f, xc);
    double mind = 1e300; int ret = 1;
    for (int j = 0; j < 8; j++)
    {
        double x[3]; for (int k = 0; k < 3; k++) x[k] = (j >> k & 1) ? it->h[k] : it->l[k];
        corner_vec(V[j], it->f, x);
        arb_zero(t); for (int i = 0; i < 4; i++) arb_addmul(t, &V[j][i], N + i, PREC);
        double dl = lb(t); if (dl < mind) mind = dl;
    }
    if (!(mind > 0)) { ret = -1; goto done; }
    /* T = 1/mind rounded up;  c' = cL / T rounded down */
    arb_set_d(T, mind); arb_inv(T, T, PREC); { double Tu = ub(T); arb_set_d(T, Tu); }
    arb_set_d(cp, it->cL); arb_div(cp, cp, T, PREC); { double c1 = lb(cp); if (c1 < 0) c1 = 0; arb_set_d(cp, c1); }
    double Mx = 0;
    for (int j = 0; j < 8; j++)
    {
        if (Jfun(J, cp, V[j], PREC)) { ret = -1; goto done; }
        double u = ub(J); if (u > Mx) Mx = u;
    }
    arb_set_d(M, Mx); arb_mul(M, M, T, PREC); *Mo = ub(M);
    arb_set_d(t, it->cU); dfun(d, t, PREC); *dUo = lb(d);
    if (Jfun(J, cp, N, PREC)) { ret = -1; goto done; }
    *Jco = arf_get_d(arb_midref(J), ARF_RND_NEAR);
    ret = (*Mo < *dUo) ? 1 : 0;
done:
    for (int j = 0; j < 8; j++) for (int i = 0; i < 4; i++) arb_clear(&V[j][i]);
    for (int i = 0; i < 4; i++) arb_clear(N + i);
    arb_clear(t); arb_clear(T); arb_clear(cp); arb_clear(J); arb_clear(d); arb_clear(M);
    return ret;
}

static double dd(double c) { return 1.5 * sqrt(2 / M_PI) / (sqrt(1 + c * c) + c); }

int main(int argc, char **argv)
{
    if (argc < 4) { fprintf(stderr, "usage: fibcover cmin cmax nbands [maxitems]\n"); return 2; }
    double cmin = atof(argv[1]), cmax = atof(argv[2]); int nb = atoi(argv[3]);
    long maxitems = argc > 4 ? atol(argv[4]) : 2000000000L;
    fib_init(PREC);
    long cap = 1 << 22; item_t *st = malloc(sizeof(item_t) * cap); long sp = 0;
    /* bands: endpoints rounded to multiples of 2^-30 (exact doubles), union = [cmin, cmax] */
    for (int b = nb - 1; b >= 0; b--) for (int f = 3; f >= 0; f--)
    {
        item_t it; it.f = f; for (int k = 0; k < 3; k++) { it.l[k] = -1; it.h[k] = 1; }
        it.cL = (b == 0) ? cmin : ldexp(floor(ldexp(cmin + (cmax - cmin) * b / nb, 30)), -30);
        it.cU = (b == nb - 1) ? cmax : ldexp(floor(ldexp(cmin + (cmax - cmin) * (b + 1) / nb, 30)), -30);
        st[sp++] = it;
    }
    long ncert = 0, nproc = 0, nfail = 0, nevalfail = 0; double worst = 1e9, worst_c = 0; time_t t0 = time(NULL);
    double cov = 0;  /* covered (band length x facet volume fraction) for progress */
    while (sp > 0 && nproc < maxitems)
    {
        item_t it = st[--sp]; nproc++;
        double M = 0, dU = 0, Jc = 0;
        int r = test_item(&it, &M, &dU, &Jc);
        double w = 0; for (int k = 0; k < 3; k++) if (it.h[k] - it.l[k] > w) w = it.h[k] - it.l[k];
        if (r == 1)
        {
            ncert++; double rel = (dU - M) / dU; if (rel < worst) { worst = rel; worst_c = it.cU; }
            double vol = (it.h[0] - it.l[0]) * (it.h[1] - it.l[1]) * (it.h[2] - it.l[2]) / 8.0;
            cov += vol * (it.cU - it.cL) / 4.0;
            continue;
        }
        if (r < 0) nevalfail++;
        /* split: band if the drop of d across the band dominates the patch slack, else the patch */
        double lossc = dd(it.cL) - dd(it.cU), lossp = (r < 0) ? 1e300 : M - Jc;
        int splitc = (lossc >= lossp) || (r < 0 && w < 1e-6);
        if (w < 1e-7 && it.cU - it.cL < 1e-12) { nfail++; fprintf(stdout, "FAIL f=%d box [%.17g,%.17g]x[%.17g,%.17g]x[%.17g,%.17g] c [%.17g,%.17g]\n", it.f, it.l[0], it.h[0], it.l[1], it.h[1], it.l[2], it.h[2], it.cL, it.cU); continue; }
        if (sp + 2 >= cap) { cap *= 2; st = realloc(st, sizeof(item_t) * cap); }
        item_t A = it, B = it;
        if (splitc) { double m = 0.5 * (it.cL + it.cU); A.cU = m; B.cL = m; }
        else { int k = 0; for (int i = 1; i < 3; i++) if (it.h[i] - it.l[i] > it.h[k] - it.l[k]) k = i; double m = 0.5 * (it.l[k] + it.h[k]); A.h[k] = m; B.l[k] = m; }
        st[sp++] = B; st[sp++] = A;
        if (nproc % 200000 == 0) { fprintf(stderr, "processed %ld certified %ld stack %ld covered %.6f of band  worst rel margin %.3e (c=%.4f)  %lds\n", nproc, ncert, sp, cov / (cmax - cmin), worst, worst_c, (long)(time(NULL) - t0)); }
    }
    printf("c in [%.17g, %.17g]: processed %ld, certified pairs %ld, failures %ld, evaluation retries %ld, stack left %ld\n", cmin, cmax, nproc, ncert, nfail, nevalfail, sp);
    printf("covered fraction %.12f, worst relative margin (d(cU) - bound)/d(cU) = %.4e at c = %.6f, time %lds\n", cov / (cmax - cmin), worst, worst_c, (long)(time(NULL) - t0));
    if (sp == 0 && nfail == 0) printf("CERTIFIED: J(c,a) < d(c) for all unit a and all c in [%.17g, %.17g]\n", cmin, cmax);
    else printf("NOT certified\n");
    return 0;
}
