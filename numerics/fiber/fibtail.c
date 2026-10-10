/* fibtail.c -- the dual fiber inequality J(c, a) <= d(c) for every unit a and every c >= 8 (lambda = 1/c, u = lambda^2).
 *
 * Analytic reduction (README, "Tail c >= 8"): with p = e + o, e(s) = A0 + B s^2 (even part), o odd,
 * O = a1^2 + a3^2, kappa = 5/4, s* = kappa/c, S0 = (sqrt6 c)^{1/2}:
 *     J <= T1 + T2 + T3,
 *     T1 = 2 phi0 lambda q(u),   q(u) = int_0^{y1} (A0 - y + B u y^2)(1 - u y^2/2 + u^2 y^4/8) dy,
 *          y1 = 2 A0 / (1 + sqrt(1 - 4 A0 B u)),
 *     T2 = 5/2 phi0 kappa^2 O / (c^2 (c - 2|B| kappa/c)),
 *     T3 = (4/sqrt6) phi0 exp(-sqrt6 c / 2),
 * and, with D(u) = (3nu/2)/(1 + sqrt(1+u)) (so that c^3 d(c) = D(u)/u and c^3 T1 = 2 phi0 q(u)/u) and h = D - 2 phi0 q:
 *     c^3 (d - T1 - T2 - T3) = phi0 (3/2)(1 - r^2 cos^2 f)/u + h'(xi) - c^3 T2 - c^3 T3,   xi in [0, u]
 * (h(0) = phi0 (3/2 - A0^2) and q(0) = A0^2/2).  The even part is (a0, a2) = r (cos t, sin t) with t = f - t0,
 * tan t0 = 1/sqrt2, so that A0 = r sqrt(3/2) cos f >= 0 for f in [-pi/2, pi/2] (A0 < 0 is the same as -p) and
 * B = r sin(f - t0)/sqrt2.  This program certifies the right-hand side > 0 on [-pi/2, pi/2] x [0,1] x [0, 1/64]
 * by interval branch and bound, and the scalar side conditions of the reduction.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "fibcore.h"
static slong PREC = 128;
static arb_t KAP, T0C, T0S, SQ15, T3MAX;

/* lower bound of c^3 (d - T1 - T2 - T3) over the box; returns arb (use lower endpoint) */
static void Fbox(arb_t F, double f0, double f1, double r0, double r1, double u0, double u1)
{
    arb_t f, r, u, U, A0, B, O, t, s, y1, D, qd, sf, cf;
    arb_init(f); arb_init(r); arb_init(u); arb_init(U); arb_init(A0); arb_init(B); arb_init(O); arb_init(t); arb_init(s);
    arb_init(y1); arb_init(D); arb_init(qd); arb_init(sf); arb_init(cf);
    arf_t a, b; arf_init(a); arf_init(b);
    arf_set_d(a, f0); arf_set_d(b, f1); arb_set_interval_arf(f, a, b, PREC);
    arf_set_d(a, r0); arf_set_d(b, r1); arb_set_interval_arf(r, a, b, PREC);
    arf_set_d(a, 0); arf_set_d(b, u1); arb_set_interval_arf(U, a, b, PREC);          /* xi in [0, u1] */
    arb_sin_cos(sf, cf, f, PREC);
    arb_mul(A0, r, SQ15, PREC); arb_mul(A0, A0, cf, PREC);
    /* sin(f - t0) = sin f cos t0 - cos f sin t0 */
    arb_mul(B, sf, T0C, PREC); arb_submul(B, cf, T0S, PREC); arb_mul(B, B, r, PREC); arb_mul(B, B, C_RSQ2, PREC);
    arb_sqr(O, r, PREC); arb_neg(O, O); arb_add_ui(O, O, 1, PREC);                   /* O = 1 - r^2 */
    /* first term: phi0 (3/2)(O + r^2 sin^2 f) / u1 */
    arb_sqr(t, sf, PREC); arb_sqr(s, r, PREC); arb_mul(t, t, s, PREC); arb_add(t, t, O, PREC);
    arb_mul_ui(t, t, 3, PREC); arb_mul_2exp_si(t, t, -1); arb_mul(t, t, C_PHI0, PREC);
    arb_set_d(s, u1); arb_div(F, t, s, PREC);
    /* h'(U) = D'(U) - 2 phi0 q'(U) */
    arb_add_ui(t, U, 1, PREC); arb_sqrt(t, t, PREC);                                  /* sqrt(1+U) */
    arb_add_ui(s, t, 1, PREC); arb_sqr(s, s, PREC); arb_mul(s, s, t, PREC); arb_mul_2exp_si(s, s, 1);
    arb_mul_ui(D, C_NU, 3, PREC); arb_mul_2exp_si(D, D, -1); arb_div(D, D, s, PREC); arb_neg(D, D);
    arb_mul(t, A0, B, PREC); arb_mul(t, t, U, PREC); arb_mul_2exp_si(t, t, 2); arb_neg(t, t); arb_add_ui(t, t, 1, PREC);
    if (!arb_is_positive(t)) { arb_indeterminate(F); goto done; }
    arb_sqrt(t, t, PREC); arb_add_ui(t, t, 1, PREC); arb_mul_2exp_si(y1, A0, 1); arb_div(y1, y1, t, PREC);
    {
        arb_poly_t G, W, dG, dW, P, Q2; arb_poly_init(G); arb_poly_init(W); arb_poly_init(dG); arb_poly_init(dW); arb_poly_init(P); arb_poly_init(Q2);
        arb_poly_set_coeff_arb(G, 0, A0); arb_set_si(t, -1); arb_poly_set_coeff_arb(G, 1, t); arb_mul(t, B, U, PREC); arb_poly_set_coeff_arb(G, 2, t);
        arb_one(t); arb_poly_set_coeff_arb(W, 0, t); arb_mul_2exp_si(t, U, -1); arb_neg(t, t); arb_poly_set_coeff_arb(W, 2, t);
        arb_sqr(t, U, PREC); arb_mul_2exp_si(t, t, -3); arb_poly_set_coeff_arb(W, 4, t);
        arb_poly_set_coeff_arb(dG, 2, B);
        arb_set_d(t, -0.5); arb_poly_set_coeff_arb(dW, 2, t); arb_mul_2exp_si(t, U, -2); arb_poly_set_coeff_arb(dW, 4, t);
        arb_poly_mul(P, dG, W, PREC); arb_poly_mul(Q2, G, dW, PREC); arb_poly_add(P, P, Q2, PREC);
        arb_poly_integral(Q2, P, PREC); arb_poly_evaluate(qd, Q2, y1, PREC);
        arb_poly_clear(G); arb_poly_clear(W); arb_poly_clear(dG); arb_poly_clear(dW); arb_poly_clear(P); arb_poly_clear(Q2);
    }
    arb_mul(qd, qd, C_PHI0, PREC); arb_mul_2exp_si(qd, qd, 1); arb_sub(D, D, qd, PREC);  /* h'(U) */
    arb_add(F, F, D, PREC);
    /* - c^3 T2 = - 5/2 phi0 kappa^2 O / (1 - 2|B| kappa u),  u in [u0,u1] */
    arf_set_d(a, u0); arf_set_d(b, u1); arb_set_interval_arf(u, a, b, PREC);
    arb_abs(t, B); arb_mul(t, t, KAP, PREC); arb_mul(t, t, u, PREC); arb_mul_2exp_si(t, t, 1); arb_neg(t, t); arb_add_ui(t, t, 1, PREC);
    if (!arb_is_positive(t)) { arb_indeterminate(F); goto done; }
    arb_sqr(s, KAP, PREC); arb_mul(s, s, O, PREC); arb_mul(s, s, C_PHI0, PREC); arb_mul_ui(s, s, 5, PREC); arb_mul_2exp_si(s, s, -1);
    arb_div(s, s, t, PREC); arb_sub(F, F, s, PREC);
    arb_sub(F, F, T3MAX, PREC);
done:
    arb_clear(f); arb_clear(r); arb_clear(u); arb_clear(U); arb_clear(A0); arb_clear(B); arb_clear(O); arb_clear(t); arb_clear(s);
    arb_clear(y1); arb_clear(D); arb_clear(qd); arb_clear(sf); arb_clear(cf); arf_clear(a); arf_clear(b);
}

typedef struct { double f0, f1, r0, r1, u0, u1; } box_t;

int main(void)
{
    fib_init(PREC);
    arb_init(KAP); arb_init(T0C); arb_init(T0S); arb_init(SQ15); arb_init(T3MAX);
    arb_set_d(KAP, 1.25);
    arb_set_ui(T0C, 2); arb_div_ui(T0C, T0C, 3, PREC); arb_sqrt(T0C, T0C, PREC);       /* cos t0 = sqrt(2/3) */
    arb_set_ui(T0S, 3); arb_rsqrt(T0S, T0S, PREC);                                      /* sin t0 = 1/sqrt3 */
    arb_set_ui(SQ15, 3); arb_mul_2exp_si(SQ15, SQ15, -1); arb_sqrt(SQ15, SQ15, PREC);
    const double C_T = 8.0, UMAX = 1.0 / 64.0;
    arb_t t, s, c; arb_init(t); arb_init(s); arb_init(c);
    int ok = 1;
    /* (S1) c^3 T3 is decreasing for c >= 8: d/dc [3 ln c - sqrt6 c/2] = 3/c - sqrt6/2 < 0 */
    arb_set_ui(t, 6); arb_sqrt(t, t, PREC); arb_mul_2exp_si(t, t, -1); arb_set_d(s, 3.0 / C_T); arb_sub(s, s, t, PREC);
    printf("(S1) 3/8 - sqrt6/2 = "); arb_printd(s, 8); printf("  %s\n", arb_is_negative(s) ? "< 0 OK" : "FAIL"); ok &= arb_is_negative(s);
    /* T3MAX = (4/sqrt6) phi0 8^3 exp(-4 sqrt6) */
    arb_set_ui(t, 6); arb_sqrt(t, t, PREC); arb_mul_ui(s, t, 4, PREC); arb_neg(s, s); arb_exp(s, s, PREC);
    arb_mul_ui(s, s, 512, PREC); arb_mul(s, s, C_PHI0, PREC); arb_mul_ui(s, s, 4, PREC); arb_div(T3MAX, s, t, PREC);
    printf("c^3 T3 <= "); arb_printd(T3MAX, 8); printf(" for c >= 8\n");
    /* (S2) localization at s*: K(kappa/c) <= kappa^2, K(s) = 3/2 + 3/2 s^2 - s^4/2 + s^6/6, for u = 1/c^2 in [0, 1/64]:
            3/2 + 3/2 k^2 u + k^6 u^3/6 <= k^2 at u = 1/64 (monotone bound, the -s^4/2 term dropped) */
    arb_set_d(c, UMAX); arb_sqr(t, KAP, PREC); arb_mul(s, t, c, PREC); arb_mul_ui(s, s, 3, PREC); arb_mul_2exp_si(s, s, -1);
    arb_add_ui(s, s, 0, PREC); { arb_t w; arb_init(w); arb_set_d(w, 1.5); arb_add(s, s, w, PREC);
      arb_pow_ui(w, KAP, 6, PREC); arb_mul(w, w, c, PREC); arb_mul(w, w, c, PREC); arb_mul(w, w, c, PREC); arb_div_ui(w, w, 6, PREC); arb_add(s, s, w, PREC); arb_clear(w); }
    arb_sub(s, t, s, PREC);
    printf("(S2) kappa^2 - K(s*) >= "); arb_printd(s, 8); printf("  %s\n", arb_is_positive(s) ? "> 0 OK" : "FAIL"); ok &= arb_is_positive(s);
    /* (S3) the other side conditions (s*^2 <= 6, sqrt(5/2) <= c, 2|B| s* < c, S0 >= 1.95) hold trivially for c >= 8 */
    printf("(S3) s*^2 = 25/(16 c^2) <= 6, sqrt(5/2) < 8, 2 (1/sqrt2)(5/4)/8 < 8, S0^2 = sqrt6 c >= 19.5 > 3.8: OK\n");
    /* branch and bound */
    long cap = 1 << 20, sp = 0, nproc = 0, ncert = 0; box_t *st = malloc(sizeof(box_t) * cap);
    int NF = 64, NR = 16;
    for (int i = 0; i < NF; i++) for (int j = 0; j < NR; j++)
    {
        box_t B = { -M_PI_2 + M_PI * i / NF, -M_PI_2 + M_PI * (i + 1) / NF, (double) j / NR, (double) (j + 1) / NR, 0, UMAX };
        if (i == 0) B.f0 = -1.5707963267948968;   /* outward: covers -pi/2 */
        if (i == NF - 1) B.f1 = 1.5707963267948968;
        st[sp++] = B;
    }
    double worst = 1e300; box_t wb = {0};
    arb_t F; arb_init(F);
    while (sp > 0)
    {
        box_t b = st[--sp]; nproc++;
        Fbox(F, b.f0, b.f1, b.r0, b.r1, b.u0, b.u1);
        if (arb_is_finite(F) && arb_is_positive(F)) { ncert++; arf_t l; arf_init(l); arb_get_lbound_arf(l, F, 60); double v = arf_get_d(l, ARF_RND_DOWN); if (v < worst) { worst = v; wb = b; } arf_clear(l); continue; }
        double wf = (b.f1 - b.f0) / M_PI, wr = b.r1 - b.r0, wu = (b.u1 - b.u0) / UMAX;
        if (wf < 1e-9 && wr < 1e-9 && wu < 1e-9) { printf("FAIL at box f [%g,%g] r [%g,%g] u [%g,%g]\n", b.f0, b.f1, b.r0, b.r1, b.u0, b.u1); ok = 0; continue; }
        if (sp + 2 >= cap) { cap *= 2; st = realloc(st, sizeof(box_t) * cap); }
        box_t A = b, C = b;
        if (wf >= wr && wf >= wu) { double m = 0.5 * (b.f0 + b.f1); A.f1 = m; C.f0 = m; }
        else if (wr >= wu) { double m = 0.5 * (b.r0 + b.r1); A.r1 = m; C.r0 = m; }
        else { double m = 0.5 * (b.u0 + b.u1); A.u1 = m; C.u0 = m; }
        st[sp++] = A; st[sp++] = C;
    }
    printf("branch and bound: %ld boxes processed, %ld certified, worst lower bound of c^3 (d - T1 - T2 - T3) = %.6e\n", nproc, ncert, worst);
    printf("  at f in [%.6f, %.6f], r in [%.6f, %.6f], u in [%.3e, %.3e]\n", wb.f0, wb.f1, wb.r0, wb.r1, wb.u0, wb.u1);
    printf(ok ? "CERTIFIED: J(c, a) < d(c) for every unit a and every c >= 8\n" : "NOT certified\n");
    return ok ? 0 : 1;
}
