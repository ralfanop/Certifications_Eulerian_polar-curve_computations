/*
 * Sprugnoli, Integers 6 (2006) A27, Theorem 3.2 (1)-(2):
 *   S1 = sum_{n>=1} (-4)^n / (n C(2n,n))   = sqrt2 ln(sqrt2 - 1) = -sqrt2 log(1 + sqrt2),
 *   S2 = sum_{n>=1} (-4)^n / (n^2 C(2n,n)) = -2 (ln(sqrt2 - 1))^2 = -2 log(1 + sqrt2)^2.
 * The terms alternate in sign and their moduli r_n/n, r_n/n^2 (r_n = 4^n/C(2n,n),
 * r_{n+1}/r_n = (2n+2)/(2n+1)) decrease for n >= 1:
 *   (r_{n+1}/(n+1)) / (r_n/n) = 2n/(2n+1) < 1,
 *   (r_{n+1}/(n+1)^2) / (r_n/n^2) = 2n^2/((2n+1)(n+1)) < 1,
 * and tend to 0 (r_n ~ sqrt(pi n)), so the value lies between two consecutive
 * partial sums.  We enclose it by the ball [S_N, S_{N+1}] (Leibniz) with N = 2^24,
 * and check that it contains the closed forms.  Slow convergence: N^{-1/2} for S1.
 */
#include <stdio.h>
#include "flint/arb.h"

int main(void)
{
    slong prec = 128, n, N = 1L << 24;
    arb_t r, t, S1, S2, P1, P2, E1, E2, L, c;
    arb_init(r); arb_init(t); arb_init(S1); arb_init(S2); arb_init(P1); arb_init(P2);
    arb_init(E1); arb_init(E2); arb_init(L); arb_init(c);
    arb_one(r); arb_zero(S1); arb_zero(S2);
    for (n = 1; n <= N + 1; n++) {
        /* r_n = r_{n-1} * 2n/(2n-1) */
        arb_mul_ui(r, r, 2 * n, prec); arb_div_ui(r, r, 2 * n - 1, prec);
        arb_set(P1, S1); arb_set(P2, S2);
        arb_div_ui(t, r, n, prec);
        if (n % 2) arb_sub(S1, S1, t, prec); else arb_add(S1, S1, t, prec);
        arb_div_ui(t, t, n, prec);
        if (n % 2) arb_sub(S2, S2, t, prec); else arb_add(S2, S2, t, prec);
    }
    /* value lies between P (= S_N) and S (= S_{N+1}) */
    arb_union(E1, P1, S1, prec); arb_union(E2, P2, S2, prec);
    arb_sqrt_ui(L, 2, prec); arb_add_ui(L, L, 1, prec); arb_log(L, L, prec);   /* log(1+sqrt2) */
    printf("N = %ld\n", N);
    arb_sqrt_ui(c, 2, prec); arb_mul(c, c, L, prec); arb_neg(c, c);
    printf("S1 enclosure  "); arb_printn(E1, 12, 0);
    printf("\n-sqrt2 log(1+sqrt2) = "); arb_printn(c, 25, 0);
    printf("\ncontained: %s\n", arb_contains(E1, c) ? "YES" : "NO");
    if (!arb_contains(E1, c)) return 1;
    arb_sqr(c, L, prec); arb_mul_si(c, c, -2, prec);
    printf("S2 enclosure  "); arb_printn(E2, 15, 0);
    printf("\n-2 log(1+sqrt2)^2   = "); arb_printn(c, 25, 0);
    printf("\ncontained: %s\n", arb_contains(E2, c) ? "YES" : "NO");
    if (!arb_contains(E2, c)) return 1;
    printf("ALL CHECKS PASSED\n");
    return 0;
}
