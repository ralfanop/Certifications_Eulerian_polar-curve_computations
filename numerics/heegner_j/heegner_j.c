/*
 * j-invariant at the CM points of the nine Gauss-Heegner numbers
 *   H = 1, 2, 3, 7, 11, 19, 43, 67, 163,
 *   tau = i sqrt(H)            (H = 1, 2),
 *   tau = (1 + i sqrt(H)) / 2  (H = 3, 7, ..., 163),
 * in Arb ball arithmetic (acb_modular_j), together with the exact checks
 *   N(27 + 19 sqrt2) = 27^2 - 2*19^2 = 7,
 *   j(i) - j(i sqrt2) = -6272 = -2^7 * 7^2.
 * By the theory of complex multiplication j(tau) is a rational integer for
 * these nine points (class number 1); the program checks that each enclosing
 * ball has radius < 1/2 and contains exactly the stated integer.
 */
#include <stdio.h>
#include "flint/arb.h"
#include "flint/acb.h"
#include "flint/acb_modular.h"
#include "flint/fmpz.h"
#include "flint/fmpz_factor.h"

int main(void)
{
    const int H[9] = {1, 2, 3, 7, 11, 19, 43, 67, 163};
    const char *expect[9] = {"1728", "8000", "0", "-3375", "-32768", "-884736",
        "-884736000", "-147197952000", "-262537412640768000"};
    slong prec = 256;
    fmpz_t J[9], e, d, n;
    acb_t tau, j;
    arb_t half;
    int k, ok = 1;

    acb_init(tau); acb_init(j); arb_init(half);
    fmpz_init(e); fmpz_init(d); fmpz_init(n);
    arb_set_d(half, 0.5);

    printf("%5s  %-26s  %s\n", "H", "certified integer j(tau)", "ball for j(tau)");
    for (k = 0; k < 9; k++) {
        fmpz_init(J[k]);
        arb_sqrt_ui(acb_imagref(tau), H[k], prec);
        if (H[k] <= 2) arb_zero(acb_realref(tau));
        else { arb_set_d(acb_realref(tau), 0.5); arb_mul_2exp_si(acb_imagref(tau), acb_imagref(tau), -1); }
        acb_modular_j(j, tau, prec);
        /* real part determines a unique integer, imaginary part contains 0 */
        if (!arb_get_unique_fmpz(J[k], acb_realref(j)) || !arb_contains_zero(acb_imagref(j))
            || mag_cmp_2exp_si(arb_radref(acb_realref(j)), -1) >= 0) {
            printf("H = %d: integer not determined\n", H[k]); ok = 0; continue;
        }
        fmpz_set_str(e, expect[k], 10);
        if (!fmpz_equal(e, J[k])) ok = 0;
        printf("%5d  ", H[k]); fmpz_print(J[k]);
        printf("%*s", (int)(28 - fmpz_sizeinbase(J[k], 10) - (fmpz_sgn(J[k]) < 0)), "");
        arb_printn(acb_realref(j), 25, 0); printf("\n");
    }

    /* exact checks */
    fmpz_sub(d, J[0], J[1]);
    printf("\nj(i) - j(i sqrt2) = "); fmpz_print(d);
    {
        fmpz_factor_t f; fmpz_factor_init(f); fmpz_factor(f, d);
        printf(" = "); fmpz_factor_print(f); printf("\n");
        fmpz_factor_clear(f);
    }
    if (fmpz_cmp_si(d, -6272) != 0) ok = 0;
    fmpz_set_si(n, 27 * 27 - 2 * 19 * 19);
    printf("N(27 + 19 sqrt2) = 27^2 - 2*19^2 = "); fmpz_print(n); printf("\n");
    if (fmpz_cmp_ui(n, 7) != 0) ok = 0;
    printf("(27 + 19 sqrt2)/(27 - 19 sqrt2) = (27 + 19 sqrt2)^2 / 7 = (1451 + 1026 sqrt2)/7\n");
    if (27*27 + 2*19*19 != 1451 || 2*27*19 != 1026) ok = 0;
    printf("7^2 divides j(i) - j(i sqrt2): %s\n", fmpz_divisible_si(d, 49) ? "YES" : "NO");
    if (!fmpz_divisible_si(d, 49)) ok = 0;

    printf("\nALL CHECKS %s\n", ok ? "PASSED" : "FAILED");
    return ok ? 0 : 1;
}
