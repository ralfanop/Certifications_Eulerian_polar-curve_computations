/*
 * Kontsevich & Zagier, "Periods" (2001), p. 797: the conjectural identity
 *
 *   20 G / pi + 1728 pi^2 Int_{sqrt2}^{inf} E4(iy) Delta(iy) / E6(iy)^2 (y^2 - 2) dy
 *       =?  log( (27 + 19 sqrt2) / (27 - 19 sqrt2) ),
 *
 * (G = Catalan's constant), whose two sides are the provable and the predicted
 * value of -G_2(i, i sqrt2)/sqrt2 for the full modular group.
 *
 * Rigorous ball arithmetic (Arb, FLINT 3):
 *  - E4 = G4/(2 zeta(4)), E6 = G6/(2 zeta(6)) from acb_modular_eisenstein,
 *    Delta from acb_modular_delta, at tau = i y;
 *  - the integral over [sqrt2, Y] by acb_calc_integrate (Petras / Gauss-Legendre
 *    with certified error bounds; the integrand is meromorphic and every
 *    evaluation on a ball containing a zero of E6 or leaving Re y > 0 is
 *    returned as non-finite, as required by acb_calc_integrate);
 *  - the tail over [Y, inf) is bounded analytically and added as an error
 *    radius (see README.md):  |integrand| <= 8 y^2 exp(-2 pi y) for y >= Y,
 *    so  tail <= 8 e^{-aY} (Y^2/a + 2Y/a^2 + 2/a^3),  a = 2 pi.
 *
 * Usage: ./kz797_arb DIGITS
 */
#include <stdio.h>
#include <stdlib.h>
#include "flint/arb.h"
#include "flint/acb.h"
#include "flint/acb_modular.h"
#include "flint/acb_calc.h"
#include "flint/arb_calc.h"


#include "flint/fmpz.h"
/* floor(x * 10^D) if the ball determines it */
static char * exact_digits(const arb_t x, slong D, slong prec)
{
    arb_t y; fmpz_t lo, hi, p10; arf_t a; char *s = NULL;
    arb_init(y); fmpz_init(lo); fmpz_init(hi); fmpz_init(p10); arf_init(a);
    fmpz_ui_pow_ui(p10, 10, D);
    arb_mul_fmpz(y, x, p10, prec);
    arb_get_lbound_arf(a, y, prec); arf_get_fmpz(lo, a, ARF_RND_FLOOR);
    arb_get_ubound_arf(a, y, prec); arf_get_fmpz(hi, a, ARF_RND_FLOOR);
    if (fmpz_equal(lo, hi)) s = fmpz_get_str(NULL, 10, lo);
    arb_clear(y); fmpz_clear(lo); fmpz_clear(hi); fmpz_clear(p10); arf_clear(a);
    return s;
}

typedef struct { arb_t z4x2, z6x2; } param_t;   /* 2 zeta(4), 2 zeta(6) */

static int f(acb_ptr res, const acb_t y, void *pp, slong order, slong prec)
{
    param_t *p = (param_t *) pp;
    acb_t tau, e4, d, y2;
    acb_ptr g;
    if (order > 1) flint_abort();
    if (!arb_is_positive(acb_realref(y))) { acb_indeterminate(res); return 0; }

    acb_init(tau); acb_init(e4); acb_init(d); acb_init(y2);
    g = _acb_vec_init(2);

    acb_mul_onei(tau, y);                          /* tau = i y */
    acb_modular_eisenstein(g, tau, 2, prec);       /* g[0]=G4, g[1]=G6 */
    acb_div_arb(g + 0, g + 0, p->z4x2, prec);      /* E4 */
    acb_div_arb(g + 1, g + 1, p->z6x2, prec);      /* E6 */
    acb_modular_delta(d, tau, prec);

    acb_mul(e4, g + 0, d, prec);                   /* E4 Delta */
    acb_sqr(g + 1, g + 1, prec);                   /* E6^2 */
    acb_div(res, e4, g + 1, prec);                 /* non-finite if E6^2 ball contains 0 */
    acb_sqr(y2, y, prec);
    acb_sub_ui(y2, y2, 2, prec);
    acb_mul(res, res, y2, prec);

    if (order == 1 && !acb_is_finite(res)) acb_indeterminate(res);

    _acb_vec_clear(g, 2);
    acb_clear(tau); acb_clear(e4); acb_clear(d); acb_clear(y2);
    return 0;
}

int main(int argc, char **argv)
{
    slong digits = (argc > 1) ? atol(argv[1]) : 100;
    slong prec = (slong)(digits * 3.33) + 80;
    slong Y;
    param_t p;
    arb_t s2, G, pi, I, tail, a, t, u, lhs, rhs, diff;
    acb_t A, B, R;
    mag_t tol;
    acb_calc_integrate_opt_t opt;

    /* Y with 8 Y^2 e^{-2 pi Y} far below 10^{-digits-20} */
    Y = (slong)((digits + 30) * 2.302585093 / 6.283185307) + 10;

    arb_init(p.z4x2); arb_init(p.z6x2);
    arb_init(s2); arb_init(G); arb_init(pi); arb_init(I); arb_init(tail);
    arb_init(a); arb_init(t); arb_init(u); arb_init(lhs); arb_init(rhs); arb_init(diff);
    acb_init(A); acb_init(B); acb_init(R);
    mag_init(tol);

    arb_zeta_ui(p.z4x2, 4, prec); arb_mul_2exp_si(p.z4x2, p.z4x2, 1);
    arb_zeta_ui(p.z6x2, 6, prec); arb_mul_2exp_si(p.z6x2, p.z6x2, 1);
    arb_sqrt_ui(s2, 2, prec);
    arb_const_catalan(G, prec);
    arb_const_pi(pi, prec);

    acb_calc_integrate_opt_init(opt);
    opt->eval_limit = WORD_MAX / 4;
    opt->depth_limit = 4 * prec;
    opt->deg_limit = prec;
    mag_set_ui_2exp_si(tol, 1, -prec + 20);

    /* integral over [sqrt2, Y], split dyadically for speed */
    arb_zero(I);
    {
        double lo = 0, hi;
        slong k = 0;
        while (1) {
            if (k == 0) acb_set_arb(A, s2); else acb_set_d(A, lo);
            hi = (k == 0) ? 2.0 : 2 * lo;
            if (hi > Y) hi = (double) Y;
            acb_set_d(B, hi);
            if (acb_calc_integrate(R, f, &p, A, B, prec, tol, opt, prec) != ARB_CALC_SUCCESS) {
                printf("integration did not converge on [%g, %g]\n", lo, hi);
                return 1;
            }
            arb_add(I, I, acb_realref(R), prec);
            if (!arb_contains_zero(acb_imagref(R)) ) { printf("nonzero imaginary part?\n"); return 1; }
            if (hi >= Y) break;
            lo = hi; k++;
        }
    }

    /* analytic tail bound over [Y, inf) */
    arb_mul_2exp_si(a, pi, 1);                       /* a = 2 pi */
    arb_set_si(t, Y); arb_sqr(t, t, prec); arb_div(t, t, a, prec);          /* Y^2/a */
    arb_set_si(u, 2 * Y); arb_div(u, u, a, prec); arb_div(u, u, a, prec);   /* 2Y/a^2 */
    arb_add(t, t, u, prec);
    arb_pow_ui(u, a, 3, prec); arb_ui_div(u, 2, u, prec);                  /* 2/a^3 */
    arb_add(t, t, u, prec);
    arb_mul_si(u, a, -Y, prec); arb_exp(u, u, prec);
    arb_mul(tail, t, u, prec); arb_mul_ui(tail, tail, 8, prec);
    arb_add_error(I, tail);

    /* lhs = 20 G/pi + 1728 pi^2 I */
    arb_mul_ui(lhs, G, 20, prec); arb_div(lhs, lhs, pi, prec);
    arb_sqr(t, pi, prec); arb_mul_ui(t, t, 1728, prec); arb_mul(t, t, I, prec);
    arb_add(lhs, lhs, t, prec);

    /* rhs = log((27 + 19 sqrt2)/(27 - 19 sqrt2)) */
    arb_mul_ui(t, s2, 19, prec);
    arb_add_ui(u, t, 27, prec);
    arb_sub_ui(t, t, 27, prec); arb_neg(t, t);
    arb_div(rhs, u, t, prec); arb_log(rhs, rhs, prec);

    arb_sub(diff, lhs, rhs, prec);

    printf("digits requested: %ld, prec: %ld bits, Y = %ld\n", digits, prec, Y);
    printf("tail bound over [Y,inf): "); arb_printn(tail, 5, 0); printf("\n");
    printf("integral I = "); arb_printn(I, digits + 5, 0); printf("\n\n");
    printf("LHS = "); arb_printn(lhs, digits + 5, 0); printf("\n\n");
    printf("RHS = "); arb_printn(rhs, digits + 5, 0); printf("\n\n");
    printf("LHS - RHS = "); arb_printn(diff, 10, 0); printf("\n");
    {
        arb_t bound; arb_init(bound);
        arb_set_ui(bound, 10); arb_pow_ui(bound, bound, digits, prec); arb_inv(bound, bound, prec);
        arb_abs(t, diff);
        arb_get_ubound_arf(arb_midref(u), t, prec); mag_zero(arb_radref(u));
        printf("|LHS - RHS| < 10^-%ld : %s\n", digits, arb_lt(u, bound) ? "YES" : "NO");
        arb_clear(bound);
    }
    printf("radius(LHS) = "); mag_printd(arb_radref(lhs), 5); printf("\n");
    /* G extracted from the identity: G_KZ = (pi/20) (RHS - 1728 pi^2 I) */
    {
        arb_t GK, Gc, w; char *dk, *dc; slong D = digits, k, agree = 0;
        arb_init(GK); arb_init(Gc); arb_init(w);
        arb_sqr(w, pi, prec); arb_mul_ui(w, w, 1728, prec); arb_mul(w, w, I, prec);
        arb_sub(GK, rhs, w, prec); arb_mul(GK, GK, pi, prec); arb_div_ui(GK, GK, 20, prec);
        arb_const_catalan(Gc, prec);
        printf("\nG from the identity: "); arb_printn(GK, 30, 0);
        printf("\nradius(G_KZ) = "); mag_printd(arb_radref(GK), 4);
        arb_sub(w, GK, Gc, prec);
        printf("\nG_KZ - G = "); arb_printn(w, 10, 0); printf("\n");
        dk = exact_digits(GK, D, prec); dc = exact_digits(Gc, D, prec);
        if (dk == NULL || dc == NULL) printf("digit string not determined at D = %ld\n", D);
        else {
            for (k = 0; dk[k] && dc[k] && dk[k] == dc[k]; k++) agree++;
            printf("exact decimals of G_KZ (truncated, %ld):\nG_KZ = 0.", D);
            for (k = 0; k < D; k++) { putchar(dk[k]); if ((k+1) % 50 == 0 && k+1 < D) printf("\n       "); else if ((k+1) % 10 == 0) putchar(' '); }
            printf("\nagreement with Catalan's G: %ld of %ld decimals\n", agree, D);
        }
        arb_clear(GK); arb_clear(Gc); arb_clear(w);
    }
    return 0;
}
