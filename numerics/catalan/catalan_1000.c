/*
 * Catalan's constant G = sum_{n>=0} (-1)^n/(2n+1)^2 to 1000 exact decimals,
 * by two independent methods in Arb ball arithmetic:
 *
 *  (1) arb_const_catalan (FLINT's own algorithm);
 *  (2) Ramanujan's series
 *        G = (pi/8) log(2 + sqrt3) + (3/8) sum_{n>=0} 1 / ((2n+1)^2 C(2n,n)),
 *      summed term by term with an explicit tail bound: for n >= 1,
 *      term(n+1)/term(n) = (n+1)/(2(2n+1)) * ((2n+1)/(2n+3))^2 <= 1/3,
 *      so the tail after the last added term t is <= t * (1/3)/(1 - 1/3) = t/2.
 *
 * The 1000 printed decimals are exact (truncated, not rounded): the program
 * checks that the whole enclosing ball lies strictly inside one interval
 * [d, d + 10^-1000).
 */
#include <stdio.h>
#include <string.h>
#include "flint/arb.h"
#include "flint/fmpz.h"

#define DIGITS 1000

/* write floor(x * 10^DIGITS) if the ball determines it, else return 0 */
static int exact_digits(char **out, const arb_t x, slong prec)
{
    arb_t y; fmpz_t lo, hi, p10;
    arf_t a;
    int ok;
    arb_init(y); fmpz_init(lo); fmpz_init(hi); fmpz_init(p10); arf_init(a);
    fmpz_ui_pow_ui(p10, 10, DIGITS);
    arb_mul_fmpz(y, x, p10, prec);
    arb_get_lbound_arf(a, y, prec); arf_get_fmpz(lo, a, ARF_RND_FLOOR);
    arb_get_ubound_arf(a, y, prec); arf_get_fmpz(hi, a, ARF_RND_FLOOR);
    ok = fmpz_equal(lo, hi);
    if (ok) *out = fmpz_get_str(NULL, 10, lo);
    arb_clear(y); fmpz_clear(lo); fmpz_clear(hi); fmpz_clear(p10); arf_clear(a);
    return ok;
}

int main(void)
{
    slong prec = 3500;
    arb_t G1, G2, pi, t, s, term, tail;
    char *d1, *d2;
    slong n, nterms;

    arb_init(G1); arb_init(G2); arb_init(pi); arb_init(t); arb_init(s);
    arb_init(term); arb_init(tail);

    /* (1) */
    arb_const_catalan(G1, prec);

    /* (2) Ramanujan */
    arb_zero(s);
    {
        fmpz_t c; fmpz_init(c);
        for (n = 0; ; n++) {
            fmpz_bin_uiui(c, 2 * n, n);
            fmpz_mul_ui(c, c, (2 * n + 1) * (2 * n + 1));
            arb_one(term); arb_div_fmpz(term, term, c, prec);
            arb_add(s, s, term, prec);
            if (n > 10 && arf_cmpabs_2exp_si(arb_midref(term), -prec - 20) < 0) break;
        }
        nterms = n + 1;
        /* tail after the last added term: next terms <= term/3 each step => <= term/2 */
        arb_set(tail, term); arb_mul_2exp_si(tail, tail, -1);
        arb_add_error(s, tail);
        fmpz_clear(c);
    }
    arb_mul_ui(s, s, 3, prec); arb_mul_2exp_si(s, s, -3);
    arb_const_pi(pi, prec);
    arb_sqrt_ui(t, 3, prec); arb_add_ui(t, t, 2, prec); arb_log(t, t, prec);
    arb_mul(t, t, pi, prec); arb_mul_2exp_si(t, t, -3);
    arb_add(G2, t, s, prec);

    if (!arb_overlaps(G1, G2)) { printf("METHODS DISAGREE\n"); return 1; }
    if (!exact_digits(&d1, G1, prec) || !exact_digits(&d2, G2, prec)) {
        printf("ball straddles a digit boundary; increase prec\n"); return 1;
    }
    if (strcmp(d1, d2) != 0) { printf("DIGIT STRINGS DIFFER\n"); return 1; }

    printf("Catalan's constant G, %d exact decimals (truncated):\n", DIGITS);
    /* 0 < G < 1, so floor(G 10^DIGITS) has exactly DIGITS digits */
    if ((slong) strlen(d1) != DIGITS) { printf("unexpected length\n"); return 1; }
    printf("G = 0.");
    for (n = 1; n <= DIGITS; n++) {
        putchar(d1[n - 1]);
        if (n % 50 == 0 && n < DIGITS) printf("\n    ");
        else if (n % 10 == 0) putchar(' ');
    }
    printf("\n\nmethod 1 (arb_const_catalan) radius: "); mag_printd(arb_radref(G1), 3);
    printf("\nmethod 2 (Ramanujan series, %ld terms) radius: ", nterms); mag_printd(arb_radref(G2), 3);
    printf("\nboth methods give the same %d decimals: YES\n", DIGITS);
    flint_free(d1); flint_free(d2);
    return 0;
}
