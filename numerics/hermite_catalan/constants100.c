/*
 * 100 certified decimals of the constants of the Hermite--Catalan--Grothendieck note.
 * Ball arithmetic (Arb/FLINT).  Each constant is enclosed in a ball; the printed
 * 100 decimals are the common truncation floor(10^100 x) of every point of the ball
 * (checked with arb_get_unique_fmpz), so they are exact truncated digits.
 *   K_R   = pi / (2 log(1+sqrt2))              Krivine's bound
 *   L     = log(1+sqrt2) = arcsinh 1
 *   c     = (2/pi) log(1+sqrt2)                Krivine's constant, sinh(pi c/2) = 1
 *   S1    = sqrt2 log(sqrt2-1)                 Sprugnoli, Theorem 3.2 (1)
 *   S2    = -2 log(1+sqrt2)^2                  Sprugnoli, Theorem 3.2 (2)
 *   |z0|  = 1/sqrt2
 *   k0    : phi_C(k0) = pi(k0+1)/8 in (0,1),   phi_C(k) = (pi/4) k 2F1(1/2,1/2;2;k^2)
 *   K_H   = 8 / (pi (k0+1))                    Haagerup's bound
 *   phi_C(k0) = pi(k0+1)/8
 *   8/pi - 1                                   where the line pi(k+1)/8 reaches 1
 */
#include <stdio.h>
#include <string.h>
#include "flint/arb.h"
#include "flint/arb_hypgeom.h"
#include "flint/fmpz.h"

#define DIG 100
static slong prec = 1200;

static int print_trunc(const char *name, const arb_t x)
{
    arb_t y, f; fmpz_t t, p; char *s; int neg;
    arb_init(y); arb_init(f); fmpz_init(t); fmpz_init(p);
    neg = arb_is_negative(x);
    if (neg) arb_neg(y, x); else arb_set(y, x);
    fmpz_ui_pow_ui(p, 10, DIG);
    arb_mul_fmpz(y, y, p, prec);
    arb_floor(f, y, prec);
    if (!arb_get_unique_fmpz(t, f)) { printf("%s: NOT UNIQUE\n", name); return 1; }
    s = fmpz_get_str(NULL, 10, t);
    {   size_t n = strlen(s); char ip[64]; const char *fr;
        if (n <= DIG) { printf("%-12s %s0.", name, neg ? "-" : " "); for (size_t i = n; i < DIG; i++) putchar('0'); printf("%s\n", s); }
        else { memcpy(ip, s, n - DIG); ip[n - DIG] = 0; fr = s + n - DIG; printf("%-12s %s%s.%s\n", name, neg ? "-" : " ", ip, fr); }
    }
    flint_free(s);
    arb_clear(y); arb_clear(f); fmpz_clear(t); fmpz_clear(p);
    return 0;
}

static void phiC(arb_t r, const arb_t k)
{
    arb_t a, b, c, z, pi;
    arb_init(a); arb_init(b); arb_init(c); arb_init(z); arb_init(pi);
    arb_set_d(a, 0.5); arb_set_d(b, 0.5); arb_set_ui(c, 2); arb_sqr(z, k, prec);
    arb_hypgeom_2f1(r, a, b, c, z, 0, prec);
    arb_const_pi(pi, prec); arb_mul(r, r, pi, prec); arb_mul(r, r, k, prec); arb_mul_2exp_si(r, r, -2);
    arb_clear(a); arb_clear(b); arb_clear(c); arb_clear(z); arb_clear(pi);
}

static void f(arb_t r, const arb_t k)          /* phi_C(k) - pi(k+1)/8 */
{
    arb_t t, pi; arb_init(t); arb_init(pi);
    phiC(r, k); arb_const_pi(pi, prec);
    arb_add_ui(t, k, 1, prec); arb_mul(t, t, pi, prec); arb_mul_2exp_si(t, t, -3);
    arb_sub(r, r, t, prec);
    arb_clear(t); arb_clear(pi);
}

int main(void)
{
    arb_t pi, s2, L, x, y, lo, hi, mid, flo, fm, k0; int err = 0, it, slo;
    arb_init(pi); arb_init(s2); arb_init(L); arb_init(x); arb_init(y);
    arb_init(lo); arb_init(hi); arb_init(mid); arb_init(flo); arb_init(fm); arb_init(k0);
    arb_const_pi(pi, prec); arb_sqrt_ui(s2, 2, prec);
    arb_add_ui(L, s2, 1, prec); arb_log(L, L, prec);                      /* log(1+sqrt2) */

    arb_mul_2exp_si(x, L, 1); arb_div(x, pi, x, prec);           err |= print_trunc("K_R", x);
                                                                 err |= print_trunc("log(1+r2)", L);
    arb_div(x, L, pi, prec); arb_mul_2exp_si(x, x, 1);           err |= print_trunc("c_Krivine", x);
    arb_sub_ui(x, s2, 1, prec); arb_log(x, x, prec); arb_mul(x, x, s2, prec); err |= print_trunc("S1", x);
    arb_sqr(x, L, prec); arb_mul_si(x, x, -2, prec);             err |= print_trunc("S2", x);
    arb_rsqrt_ui(x, 2, prec);                                    err |= print_trunc("|z0|", x);

    /* k0 by bisection on [0.8, 0.83] with certified signs */
    arb_set_d(lo, 0.8); arb_set_d(hi, 0.83);
    f(flo, lo); f(fm, hi);
    if (!(arb_is_negative(flo) && arb_is_positive(fm)) && !(arb_is_positive(flo) && arb_is_negative(fm)))
    { printf("no certified sign change\n"); return 1; }
    slo = arb_sgn_nonzero(flo);
    for (it = 0; it < 420; it++) {
        arb_add(mid, lo, hi, prec); arb_mul_2exp_si(mid, mid, -1); arb_get_mid_arb(mid, mid);
        f(fm, mid);
        if (!(arb_is_positive(fm) || arb_is_negative(fm))) { printf("sign undecided at step %d\n", it); return 1; }
        if (arb_sgn_nonzero(fm) == slo) arb_set(lo, mid); else arb_set(hi, mid);
    }
    arb_union(k0, lo, hi, prec);
    printf("k0 enclosure radius ~ 2^-%d\n", 420 + 5);
                                                                 err |= print_trunc("k0", k0);
    arb_add_ui(x, k0, 1, prec); arb_mul(x, x, pi, prec); arb_ui_div(x, 8, x, prec); err |= print_trunc("K_H", x);
    arb_add_ui(x, k0, 1, prec); arb_mul(x, x, pi, prec); arb_mul_2exp_si(x, x, -3); err |= print_trunc("phiC(k0)", x);
    arb_ui_div(x, 8, pi, prec); arb_sub_ui(x, x, 1, prec);       err |= print_trunc("8/pi-1", x);
    printf(err ? "SOME DIGITS NOT CERTIFIED\n" : "ALL 100-DIGIT TRUNCATIONS CERTIFIED\n");
    return err;
}
