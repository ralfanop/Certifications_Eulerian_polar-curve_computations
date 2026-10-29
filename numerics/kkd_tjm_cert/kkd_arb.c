/* Certified decimals of the TJM version of "Explicit identities connecting Krivine's Grothendieck bound,
   Koenig's bilinear form, and quadratic Dirichlet L-series" (R. Alfano), 16 October 2026.
   Arb ball arithmetic (FLINT 3.3.1).  For every displayed decimal d with k decimals the program
   encloses the exact quantity x in a ball and reports whether the ball lies inside the rounding cell
   (d - 10^-k/2, d + 10^-k/2) ["ROUNDED"] and/or inside the truncation cell [d, d + 10^-k) for x > 0
   ["TRUNCATED"].  It also checks two closed forms against independent evaluations. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/acb_poly.h>
#include <flint/acb_dirichlet.h>
#include <flint/arb_hypgeom.h>

static slong prec = 1024;

/* t = x*10^k - D, where d = D/10^k is the decimal string (sign handled) */
static void check(const char *name, const char *eq, const char *dec, const arb_t x)
{
    char buf[256]; strcpy(buf, dec);
    int neg = (buf[0] == '-'); char *p = buf + neg;
    char *dot = strchr(p, '.'); slong k = dot ? (slong) strlen(dot + 1) : 0;
    char digits[256]; slong j = 0;
    for (char *q = p; *q; q++) if (*q != '.') digits[j++] = *q;
    digits[j] = 0;
    fmpz_t D, ten; fmpz_init(D); fmpz_init(ten);
    fmpz_set_str(D, digits, 10); if (neg) fmpz_neg(D, D);
    fmpz_set_ui(ten, 10); fmpz_pow_ui(ten, ten, k);
    arb_t t, half, zero, one, a; arb_init(t); arb_init(half); arb_init(zero); arb_init(one); arb_init(a);
    arb_mul_fmpz(t, x, ten, prec); arb_sub_fmpz(t, t, D, prec);
    arb_set_d(half, 0.5); arb_zero(zero); arb_one(one);
    arb_neg(a, half);
    int rounded = arb_gt(t, a) && arb_lt(t, half);
    int trunc;
    if (!neg) trunc = arb_ge(t, zero) && arb_lt(t, one);
    else { arb_neg(a, one); trunc = arb_gt(t, a) && arb_le(t, zero); }
    printf("%-28s (%s)  printed %s\n    enclosure ", name, eq, dec);
    arb_printn(x, k + 15, 0);
    printf("\n    %s%s\n", rounded ? "ROUNDED: certified" : "NOT correctly rounded",
           trunc ? (rounded ? "; also TRUNCATED" : "; TRUNCATED: certified as truncation") : "");
    fmpz_clear(D); fmpz_clear(ten); arb_clear(t); arb_clear(half); arb_clear(zero); arb_clear(one); arb_clear(a);
}

/* coefficient c[i] of zeta(s+x, a) at s, deflate flag */
static void zeta_coeffs(acb_ptr c, slong len, double s, const arb_t a, int deflate)
{
    acb_poly_t S, Z; acb_t aa; acb_poly_init(S); acb_poly_init(Z); acb_init(aa);
    acb_poly_set_coeff_si(S, 1, 1); { acb_t s0; acb_init(s0); acb_set_d(s0, s); acb_poly_set_coeff_acb(S, 0, s0); acb_clear(s0); }
    acb_set_arb(aa, a);
    acb_poly_zeta_series(Z, S, aa, deflate, len, prec);
    for (slong i = 0; i < len; i++) acb_poly_get_coeff_acb(c + i, Z, i);
    acb_poly_clear(S); acb_poly_clear(Z); acb_clear(aa);
}

int main(int argc, char **argv)
{
    if (argc > 1) prec = atol(argv[1]);
    arb_t pi, s2, L, x, y, g, ln2, lnpi, tmp; acb_t z;
    arb_init(pi); arb_init(s2); arb_init(L); arb_init(x); arb_init(y); arb_init(g); arb_init(ln2); arb_init(lnpi); arb_init(tmp); acb_init(z);
    arb_const_pi(pi, prec); arb_sqrt_ui(s2, 2, prec);
    arb_add_ui(L, s2, 1, prec); arb_log(L, L, prec);              /* L = log(1+sqrt2) */
    arb_const_euler(g, prec); arb_const_log2(ln2, prec); arb_log(lnpi, pi, prec);
    printf("Arb ball arithmetic, FLINT %s, precision %ld bits\n\n", FLINT_VERSION, prec);

    arb_sqrt_ui(x, 8, prec); arb_mul(x, x, L, prec); check("I_1 = sqrt8 log(1+sqrt2)", "6", "2.49290", x);
    arb_mul_2exp_si(x, L, 1); arb_div(x, x, pi, prec); check("2 log(1+sqrt2)/pi", "9", "0.561100", x);
    arb_div(x, L, s2, prec); check("M_0 = L_8(1)", "11, 82", "0.623225", x);
    arb_mul(x, s2, L, prec); arb_div(x, x, pi, prec); arb_div(x, x, pi, prec); arb_div_ui(x, x, 8, prec);
        check("sqrt2 log(1+sqrt2)/(8 pi^2)", "25", "0.015786", x);
    arb_mul_2exp_si(y, pi, 1); arb_sqrt(y, y, prec); arb_mul(y, y, s2, prec); arb_div(x, L, y, prec);
        check("log(1+sqrt2)/(sqrt2 sqrt(2pi))", "27", "0.24863", x);
    arb_mul(y, pi, pi, prec); arb_mul(y, y, s2, prec); arb_div(x, L, y, prec);
        check("log(1+sqrt2)/(sqrt2 pi^2)", "29", "0.0631459", x);
    arb_sqrt(y, pi, prec); arb_mul_2exp_si(x, L, 1); arb_div(x, x, y, prec);
        check("2 log(1+sqrt2)/sqrt(pi)", "31", "0.99452", x);

    /* gamma_1(1/8) */
    { fmpz_t n; fmpz_init_set_ui(n, 1); acb_t a; acb_init(a); acb_set_ui(a, 1); acb_div_ui(a, a, 8, prec);
      acb_dirichlet_stieltjes(z, n, a, prec); arb_set(x, acb_realref(z));
      check("gamma_1(1/8)", "33", "-16.64171976", x);
      /* Blagouchine's closed form as printed in (33) */
      acb_t g1; acb_init(g1); acb_one(a); acb_dirichlet_stieltjes(g1, n, a, prec);
      arb_t a8, r, lg; arb_init(a8); arb_init(r); arb_init(lg);
      acb_struct c[3]; for (int i = 0; i < 3; i++) acb_init(c + i);
      arb_set_ui(a8, 1); arb_div_ui(a8, a8, 8, prec); zeta_coeffs(c, 3, 0.0, a8, 0); arb_mul_2exp_si(r, acb_realref(c + 2), 1);
      arb_set_ui(a8, 7); arb_div_ui(a8, a8, 8, prec); zeta_coeffs(c, 3, 0.0, a8, 0); arb_mul_2exp_si(tmp, acb_realref(c + 2), 1);
      arb_add(r, r, tmp, prec); arb_mul(r, r, s2, prec);                       /* sqrt2 [zeta''(0,1/8)+zeta''(0,7/8)] */
      arb_add(y, acb_realref(g1), r, prec);
      arb_set_ui(a8, 1); arb_div_ui(a8, a8, 8, prec); arb_lgamma(lg, a8, prec);
      arb_sqrt_ui(tmp, 8, prec); arb_mul(tmp, tmp, pi, prec); arb_mul(tmp, tmp, lg, prec); arb_add(y, y, tmp, prec);
      arb_set_ui(a8, 1); arb_div_ui(a8, a8, 4, prec); arb_lgamma(lg, a8, prec);
      arb_sub_ui(tmp, s2, 1, prec); arb_neg(tmp, tmp); arb_mul(tmp, tmp, s2, prec); arb_mul(tmp, tmp, pi, prec); arb_mul(tmp, tmp, lg, prec);
      arb_sub(y, y, tmp, prec);                                                 /* - sqrt2 pi (1-sqrt2) log Gamma(1/4) */
      arb_add_ui(tmp, s2, 1, prec); arb_mul(tmp, tmp, pi, prec); arb_mul_2exp_si(tmp, tmp, -1);
      arb_addmul_ui(tmp, ln2, 4, prec); arb_addmul(tmp, s2, L, prec); arb_mul(tmp, tmp, g, prec); arb_sub(y, y, tmp, prec);
      arb_set(tmp, pi); arb_addmul_ui(tmp, ln2, 8, prec); arb_addmul_ui(tmp, lnpi, 2, prec); arb_div(tmp, tmp, s2, prec); arb_mul(tmp, tmp, L, prec);
      arb_sub(y, y, tmp, prec);
      arb_sub_ui(tmp, s2, 4, prec); arb_neg(tmp, tmp); arb_mul_ui(tmp, tmp, 7, prec); arb_div_ui(tmp, tmp, 4, prec);
      arb_mul(tmp, tmp, ln2, prec); arb_mul(tmp, tmp, ln2, prec); arb_sub(y, y, tmp, prec);
      arb_mul(tmp, ln2, lnpi, prec); arb_div(tmp, tmp, s2, prec); arb_add(y, y, tmp, prec);
      arb_mul_ui(tmp, s2, 11, prec); arb_add_ui(tmp, tmp, 10, prec); arb_mul(tmp, tmp, pi, prec); arb_div_ui(tmp, tmp, 4, prec);
      arb_mul(tmp, tmp, ln2, prec); arb_sub(y, y, tmp, prec);
      arb_sqrt_ui(tmp, 8, prec); arb_add_ui(tmp, tmp, 3, prec); arb_mul(tmp, tmp, pi, prec); arb_mul_2exp_si(tmp, tmp, -1);
      arb_mul(tmp, tmp, lnpi, prec); arb_sub(y, y, tmp, prec);
      arb_sub(tmp, y, x, prec);
      printf("    closed form (33) as printed minus gamma_1(1/8): "); arb_printn(tmp, 20, 0); printf("\n\n");
      for (int i = 0; i < 3; i++) acb_clear(c + i);
      arb_clear(a8); arb_clear(r); arb_clear(lg); acb_clear(g1); acb_clear(a); fmpz_clear(n); }

    /* gamma_8 = gamma + L'(1,chi_8)/L(1,chi_8);  L(s,chi_8) = 8^-s sum chi(a) zeta(s,a/8), chi = (1,3,5,7) -> (+,-,-,+) */
    { acb_struct c[2]; acb_init(c); acb_init(c + 1); arb_t D0, D1, a8; arb_init(D0); arb_init(D1); arb_init(a8);
      int chi[4] = {1, -1, -1, 1}; arb_zero(D0); arb_zero(D1);
      for (int i = 0; i < 4; i++) { arb_set_ui(a8, 2 * i + 1); arb_div_ui(a8, a8, 8, prec);
          zeta_coeffs(c, 2, 1.0, a8, 1);
          if (chi[i] > 0) { arb_add(D0, D0, acb_realref(c), prec); arb_add(D1, D1, acb_realref(c + 1), prec); }
          else { arb_sub(D0, D0, acb_realref(c), prec); arb_sub(D1, D1, acb_realref(c + 1), prec); } }
      /* L(1) = D0/8, L'(1) = (D1 - log8 D0)/8 ; ratio L'/L = D1/D0 - log 8 */
      arb_div(x, D1, D0, prec); arb_mul_ui(tmp, ln2, 3, prec); arb_sub(x, x, tmp, prec); arb_add(x, x, g, prec);
      arb_div_ui(y, D0, 8, prec); arb_div(tmp, L, s2, prec); arb_sub(tmp, y, tmp, prec);
      printf("L_8(1) from Hurwitz minus log(1+sqrt2)/sqrt2: "); arb_printn(tmp, 10, 0); printf("\n");
      check("gamma_8 (Euler-Kronecker)", "40", "1.20933063094138118664026424093547097334700909059315456011578210585217390057", x);
      /* (39): gamma_8 = log(2 pi e^{2 gamma}) + Rsum/(2 log(1+sqrt2)), R(x) = -zeta''(0,x) */
      acb_struct cc[3]; for (int i = 0; i < 3; i++) acb_init(cc + i); arb_t R; arb_init(R); arb_zero(R);
      for (int i = 0; i < 4; i++) { arb_set_ui(a8, 2 * i + 1); arb_div_ui(a8, a8, 8, prec); zeta_coeffs(cc, 3, 0.0, a8, 0);
          arb_mul_2exp_si(tmp, acb_realref(cc + 2), 1); arb_neg(tmp, tmp);
          if (chi[i] > 0) arb_add(R, R, tmp, prec); else arb_sub(R, R, tmp, prec); }
      arb_mul_2exp_si(y, pi, 1); arb_log(y, y, prec); arb_addmul_ui(y, g, 2, prec);
      arb_mul_2exp_si(tmp, L, 1); arb_div(tmp, R, tmp, prec); arb_add(y, y, tmp, prec);
      arb_sub(tmp, y, x, prec);
      printf("    (39) log(2 pi e^{2 gamma}) + Rsum/(2 log(1+sqrt2)) minus gamma_8: "); arb_printn(tmp, 20, 0); printf("\n\n");
      for (int i = 0; i < 3; i++) acb_clear(cc + i); arb_clear(R);
      acb_clear(c); acb_clear(c + 1); arb_clear(D0); arb_clear(D1); arb_clear(a8); }

    check("log(1+sqrt2) = 2F1(1/2,1/2;3/2;-1)", "64", "0.88137", L);
    arb_mul_2exp_si(x, pi, -1); check("pi/2 = 2F1(1/2,1/2;3/2;1)", "65", "1.57080", x);
    arb_div(x, x, L, prec); check("K_R = pi/(2 log(1+sqrt2))", "66", "1.78221", x);
    arb_sqrt_ui(y, 8, prec); arb_div(x, pi, y, prec); check("L_{-8}(1) = pi/sqrt8", "83", "1.11072", x);
    arb_mul_2exp_si(x, pi, 1); arb_sqrt(x, x, prec); check("prod k = sqrt(2 pi)", "84", "2.50663", x);
    arb_mul(x, pi, pi, prec); arb_mul_2exp_si(x, x, 2); check("prod p = 4 pi^2", "85", "39.47842", x);
    arb_mul_2exp_si(x, pi, 1); arb_inv(x, x, prec); check("P_A = 1/(2 pi)", "86", "0.15915", x);
    arb_set_ui(x, 1); arb_div_ui(x, x, 2, prec); arb_atan(x, x, prec); arb_div(x, x, pi, prec);
        check("P_gamma = arctan(1/2)/pi", "88", "0.14758", x);

    flint_cleanup();
    return 0;
}
