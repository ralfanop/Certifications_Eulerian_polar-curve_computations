/*
 * Ball-arithmetic checks (Arb, FLINT 3) of two series in the type-B Catalan
 * numbers C(2k,k):
 *
 *  (1) Krivine:  log(1 + sqrt2) = arcsinh(1) = sum_{k>=0} (-1)^k C(2k,k) / (4^k (2k+1)).
 *      The terms b_k = C(2k,k)/(4^k(2k+1)) decrease to 0 (b_{k+1}/b_k =
 *      (2k+1)^2/((2k+2)(2k+3)) < 1), so the alternating tail after N terms
 *      lies between 0 and (-1)^N b_N.  The convergence is slow (b_k ~ k^{-3/2}),
 *      so we use N = 2^22 terms and also the Euler-type average of two partial
 *      sums, whose error is bounded by b_N.
 *
 *  (2) Haagerup (complex Grothendieck constant):
 *        phi_C(t) = t int_0^{pi/2} cos^2(s) / sqrt(1 - t^2 sin^2(s)) ds
 *                 = (pi/4) sum_k C(2k,k) C_k t^{2k+1} / 16^k,
 *      at t = 1/2, 9/10, 99/100.  Integral by acb_calc_integrate (certified);
 *      series with geometric tail bound: a_{k+1}/a_k <= t^2, so
 *      tail after K terms <= a_K t^2 / (1 - t^2).
 */
#include <stdio.h>
#include "flint/arb.h"
#include "flint/acb.h"
#include "flint/acb_calc.h"
#include "flint/arb_calc.h"

static int integrand(acb_ptr res, const acb_t s, void *p, slong order, slong prec)
{
    const arb_struct *t = (const arb_struct *) p;
    acb_t c, sn, w;
    if (order > 1) flint_abort();
    acb_init(c); acb_init(sn); acb_init(w);
    acb_sin_cos(sn, c, s, prec);
    acb_sqr(sn, sn, prec);
    acb_mul_arb(sn, sn, t, prec); acb_mul_arb(sn, sn, t, prec);      /* t^2 sin^2 */
    acb_one(w); acb_sub(w, w, sn, prec);
    if (order == 1) {                     /* branch cut of sqrt: require Re(w) > 0 */
        if (!arb_is_positive(acb_realref(w))) { acb_indeterminate(res); goto done; }
    }
    acb_rsqrt(w, w, prec);
    acb_sqr(c, c, prec);
    acb_mul(res, c, w, prec);
done:
    acb_clear(c); acb_clear(sn); acb_clear(w);
    return 0;
}

int main(void)
{
    slong prec = 200;
    arb_t S, b, ratio, x, bound, pi, lg;

    arb_init(S); arb_init(b); arb_init(ratio); arb_init(x); arb_init(bound);
    arb_init(pi); arb_init(lg);
    arb_const_pi(pi, prec);

    /* (1) Krivine series */
    {
        slong N = 1L << 22, k;
        arb_t Sprev;
        arb_init(Sprev);
        arb_zero(S); arb_one(b);                         /* b_0 = 1 */
        for (k = 0; k < N; k++) {
            arb_set(Sprev, S);
            if (k % 2 == 0) arb_add(S, S, b, prec); else arb_sub(S, S, b, prec);
            /* b_{k+1} = b_k (2k+1)^2 / ((2k+2)(2k+3)) */
            arb_mul_ui(b, b, (2 * k + 1) * (2 * k + 1), prec);
            arb_div_ui(b, b, (2 * k + 2), prec);
            arb_div_ui(b, b, (2 * k + 3), prec);
        }
        /* S = S_N, b = b_N; true value lies between S_N and S_N + (-1)^N b_N = S_N + b_N (N even) */
        arb_set(x, S);
        arb_mul_2exp_si(bound, b, -1);
        arb_add(x, x, bound, prec);                     /* midpoint S_N + b_N/2 */
        arb_add_error(x, bound);                        /* +- b_N/2 */
        arb_sqrt_ui(lg, 2, prec); arb_add_ui(lg, lg, 1, prec); arb_log(lg, lg, prec);
        printf("(1) N = %ld terms\n    series enclosure  ", N); arb_printn(x, 15, 0);
        printf("\n    log(1+sqrt2)      "); arb_printn(lg, 30, 0);
        printf("\n    contained: %s\n", arb_overlaps(x, lg) ? "YES" : "NO");
        if (!arb_overlaps(x, lg)) return 1;
        arb_div(bound, pi, lg, prec); arb_mul_2exp_si(bound, bound, -1);
        printf("    Krivine pi/(2 log(1+sqrt2)) = "); arb_printn(bound, 30, 0); printf("\n");
        arb_clear(Sprev);
    }

    /* (2) Haagerup series vs integral */
    {
        const slong num[3] = {1, 9, 99}, den[3] = {2, 10, 100};
        int i;
        for (i = 0; i < 3; i++) {
            arb_t t, t2, a, ser, tail, val;
            acb_t A, B, R;
            mag_t tol;
            acb_calc_integrate_opt_t opt;
            slong k, K;
            arb_init(t); arb_init(t2); arb_init(a); arb_init(ser); arb_init(tail); arb_init(val);
            acb_init(A); acb_init(B); acb_init(R); mag_init(tol);
            acb_calc_integrate_opt_init(opt);

            arb_set_si(t, num[i]); arb_div_si(t, t, den[i], prec);
            arb_sqr(t2, t, prec);

            /* integral */
            acb_zero(A); acb_set_arb(B, pi); acb_mul_2exp_si(B, B, -1);
            mag_set_ui_2exp_si(tol, 1, -prec);
            if (acb_calc_integrate(R, integrand, t, A, B, prec, tol, opt, prec) != ARB_CALC_SUCCESS)
            { printf("integration failed\n"); return 1; }
            arb_mul(val, acb_realref(R), t, prec);

            /* series: a_k = C(2k,k)^2/((k+1) 16^k) t^{2k+1};  a_{k+1}/a_k = ((2k+1)/(2k+2))^2 (k+1)/(k+2) t^2 <= t^2 */
            K = 20000;
            arb_set(a, t); arb_zero(ser);
            for (k = 0; k < K; k++) {
                arb_add(ser, ser, a, prec);
                arb_mul_ui(a, a, (2 * k + 1) * (2 * k + 1), prec);
                arb_div_ui(a, a, (2 * k + 2) * (2 * k + 2), prec);
                arb_mul_ui(a, a, k + 1, prec);
                arb_div_ui(a, a, k + 2, prec);
                arb_mul(a, a, t2, prec);
            }
            /* a = a_K; tail <= a_K / (1 - t^2) */
            arb_one(tail); arb_sub(tail, tail, t2, prec); arb_div(tail, a, tail, prec);
            arb_add_error(ser, tail);
            arb_mul(ser, ser, pi, prec); arb_mul_2exp_si(ser, ser, -2);

            printf("(2) t = %ld/%ld\n    integral  ", num[i], den[i]); arb_printn(val, 40, 0);
            printf("\n    series    "); arb_printn(ser, 40, 0);
            printf("\n    overlap: %s\n", arb_overlaps(val, ser) ? "YES" : "NO");
            if (!arb_overlaps(val, ser)) return 1;

            arb_clear(t); arb_clear(t2); arb_clear(a); arb_clear(ser); arb_clear(tail); arb_clear(val);
            acb_clear(A); acb_clear(B); acb_clear(R); mag_clear(tol);
        }
    }
    printf("ALL BALL CHECKS PASSED\n");
    return 0;
}
