/*
 * Haagerup's bound for the complex Grothendieck constant (Israel J. Math. 60, 1987):
 *   K_G^C <= 8 / (pi (k0 + 1)),  k0 in (0,1) the solution of  phi_C(k) = pi (k + 1) / 8,
 *   phi_C(k) = k int_0^{pi/2} cos^2 t (1 - k^2 sin^2 t)^{-1/2} dt
 *            = (pi/4) sum_{j>=0} C(2j,j) C_j k^{2j+1} / 16^j      (see exact_checks.py).
 * Ball arithmetic (Arb): phi_C by the type-B/type-A Catalan series with the
 * geometric tail bound a_J k^2/(1 - k^2); a root of f(k) = phi_C(k) - pi(k+1)/8 is
 * isolated by bisection with certified signs of f at the end points, and the
 * bound is enclosed.  (Uniqueness of k0 in (0,1) is part of Haagerup's theorem.)
 */
#include <stdio.h>
#include "flint/arb.h"

static void phiC(arb_t res, const arb_t k, slong prec)
{
    arb_t a, k2, tail, s; slong j;
    arb_init(a); arb_init(k2); arb_init(tail); arb_init(s);
    arb_sqr(k2, k, prec);
    arb_set(a, k); arb_zero(s);
    for (j = 0; j < 4 * prec; j++) {               /* k <= 0.9: ratio <= 0.81 */
        arb_add(s, s, a, prec);
        arb_mul_ui(a, a, (2 * j + 1) * (2 * j + 1), prec);
        arb_div_ui(a, a, (2 * j + 2) * (2 * j + 2), prec);
        arb_mul_ui(a, a, j + 1, prec);
        arb_div_ui(a, a, j + 2, prec);
        arb_mul(a, a, k2, prec);
    }
    arb_one(tail); arb_sub(tail, tail, k2, prec); arb_div(tail, a, tail, prec);
    arb_add_error(s, tail);
    arb_const_pi(res, prec); arb_mul(res, res, s, prec); arb_mul_2exp_si(res, res, -2);
    arb_clear(a); arb_clear(k2); arb_clear(tail); arb_clear(s);
}

static void f(arb_t res, const arb_t k, slong prec)     /* phi_C(k) - pi(k+1)/8 */
{
    arb_t r; arb_init(r);
    phiC(res, k, prec);
    arb_add_ui(r, k, 1, prec); arb_t pi; arb_init(pi); arb_const_pi(pi, prec);
    arb_mul(r, r, pi, prec); arb_mul_2exp_si(r, r, -3);
    arb_sub(res, res, r, prec);
    arb_clear(r); arb_clear(pi);
}

int main(void)
{
    slong prec = 256, it;
    arb_t lo, hi, mid, flo, fmid, k0, K, pi;
    arb_init(lo); arb_init(hi); arb_init(mid); arb_init(flo); arb_init(fmid);
    arb_init(k0); arb_init(K); arb_init(pi);
    arb_set_d(lo, 0.5); arb_set_d(hi, 0.9);
    f(flo, lo, prec); f(fmid, hi, prec);
    if (!(arb_is_negative(flo) || arb_is_positive(flo)) || arb_sgn_nonzero(flo) == arb_sgn_nonzero(fmid))
    { printf("no certified sign change on [0.5, 0.9]\n"); return 1; }
    for (it = 0; it < 200; it++) {
        arb_add(mid, lo, hi, prec); arb_mul_2exp_si(mid, mid, -1);
        arb_get_mid_arb(mid, mid);
        f(fmid, mid, prec);
        if (!(arb_is_positive(fmid) || arb_is_negative(fmid))) break;
        if (arb_sgn_nonzero(fmid) == arb_sgn_nonzero(flo)) { arb_set(lo, mid); arb_set(flo, fmid); }
        else arb_set(hi, mid);
    }
    arb_union(k0, lo, hi, prec);
    arb_const_pi(pi, prec);
    arb_add_ui(K, k0, 1, prec); arb_mul(K, K, pi, prec); arb_ui_div(K, 8, K, prec);
    printf("bisection steps with certified signs: %ld\n", it);
    printf("k0          = "); arb_printn(k0, 40, 0); printf("\n");
    printf("8/(pi(k0+1)) = "); arb_printn(K, 40, 0); printf("\n");
    return 0;
}
