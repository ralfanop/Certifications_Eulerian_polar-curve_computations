/*
  certify.c -- rigorous certification of Heilman's 2D graph-threshold improvement K_G <= K_Kr - eps.

  Input: the enclosures of the Hermite coefficients alpha^f_{m,n}, alpha^g_{m,n} (m + n <= N) from alpha.c.

     C_k   = (pi/2) sum_{m+n=k} alpha^f_{m,n} alpha^g_{m,n}        H(z) = sum_k C_k z^k = (pi/2) H_{f,g}(z)
     S^f_k = sum_{m+n=k} (alpha^f_{m,n})^2  (Parseval energies, sum over all k = 1)
     b_n   = coefficients of the compositional inverse H^{-1}       (arb_poly_revert_series)
     A_N(gamma) = sum_{n<=N} |b_n| gamma^n

  Analytic tail (Rouche).  E = H - arcsin, phi(zeta) = E(sin zeta) = sum_j phi_j zeta^j, where
  phi_j = sum_{k<=j} e_k [zeta^j] sin^k zeta is exact from e_k = C_k - arcsin_k (k <= J <= N).
     delta := sup_{|zeta|=s} |sum_{j<=J} phi_j zeta^j| + M' (s/rho')^{J+1} / (1 - s/rho')   >= sup_{|zeta|=s} |phi|
  with M' >= sup_{|zeta|=rho'} |phi| from mbound.c.  Then H^{-1} = sin o G^{-1}, G(zeta) = zeta + phi(zeta),
  is analytic on |w| < s - delta with |H^{-1}| <= sinh(s), so for R' < s - delta and q = gamma/R' < 1
     sum_{n>N} |b_n| gamma^n <= sinh(s) q^{N+1} / (1 - q).

  usage: certify alphaA alphaB N prec J s rho' M' [eps [bounds_out]]
  bounds_out receives, as integers m meaning m * 10^-D: upper bound of the polynomial sup,
  and for odd n <= N upper and lower bounds of |b_n|.
*/
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <flint/arb.h>
#include <flint/arb_poly.h>
#include <flint/acb.h>
#include <flint/fmpz.h>

static slong prec, N;
static arb_poly_t B;

static void load(arb_ptr A, slong M, const char *fn)
{
    FILE *f = fopen(fn, "r"); long m, n; static char buf[100000];
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    for (slong i = 0; i < M * M; i++) arb_zero(A + i);
    while (fscanf(f, "%ld %ld %99999[^\n]", &m, &n, buf) == 3)
        if (m < M && n < M) { if (arb_load_str(A + m * M + n, buf)) { fprintf(stderr, "load err\n"); exit(1); } }
    fclose(f);
}

static void eval_poly(acb_t res, const arb_poly_t P, const acb_t z)
{
    acb_t pz, tq; acb_init(pz); acb_init(tq); acb_one(pz); acb_zero(res);
    for (slong j = 0; j < arb_poly_length(P); j++)
    { acb_set_arb(tq, arb_poly_get_coeff_ptr(P, j)); acb_mul(tq, tq, pz, prec); acb_add(res, res, tq, prec); acb_mul(pz, pz, z, prec); }
    acb_clear(pz); acb_clear(tq);
}

/* A_N(g) = sum_{n<=N} |b_n| g^n for an exact point g */
static void A_N(arb_t A, const arb_t g)
{
    arb_t gp, x; arb_init(gp); arb_init(x);
    arb_zero(A); arb_one(gp);
    for (slong n = 1; n <= N; n++)
    { arb_mul(gp, gp, g, prec); arb_poly_get_coeff_arb(x, B, n); arb_abs(x, x); arb_mul(x, x, gp, prec); arb_add(A, A, x, prec); }
    arb_clear(gp); arb_clear(x);
}


/* ceil(ub(x) * 10^D) and floor(lb(x) * 10^D) as decimal integers */
static void put_up(FILE *f, const char *lab, const arb_t x, slong D)
{
    arb_t y; fmpz_t m; arf_t u; arb_init(y); fmpz_init(m); arf_init(u);
    arb_set_ui(y, 10); arb_pow_ui(y, y, D, prec); arb_mul(y, y, x, prec);
    arb_get_ubound_arf(u, y, prec); arf_get_fmpz(m, u, ARF_RND_CEIL);
    fprintf(f, "%s ", lab); fmpz_fprint(f, m); fprintf(f, " %ld\n", D);
    arb_clear(y); fmpz_clear(m); arf_clear(u);
}
static void put_lo(FILE *f, const char *lab, const arb_t x, slong D)
{
    arb_t y; fmpz_t m; arf_t u; arb_init(y); fmpz_init(m); arf_init(u);
    arb_set_ui(y, 10); arb_pow_ui(y, y, D, prec); arb_mul(y, y, x, prec);
    arb_get_lbound_arf(u, y, prec); arf_get_fmpz(m, u, ARF_RND_FLOOR);
    if (fmpz_sgn(m) < 0) fmpz_zero(m);
    fprintf(f, "%s ", lab); fmpz_fprint(f, m); fprintf(f, " %ld\n", D);
    arb_clear(y); fmpz_clear(m); arf_clear(u);
}

/* tail(g) = sinh(s) q^{N+1}/(1-q), q = g/R' ; returns 0 and sets T if q < 1 */
static int tail_b(arb_t T, const arb_t g, const arb_t Rp, const arb_t sh)
{
    arb_t q, t; arb_init(q); arb_init(t);
    arb_div(q, g, Rp, prec);
    arb_sub_ui(t, q, 1, prec);
    if (!arb_is_negative(t)) { arb_clear(q); arb_clear(t); return 1; }
    arb_pow_ui(T, q, N + 1, prec); arb_neg(t, t); arb_div(T, T, t, prec); arb_mul(T, T, sh, prec);
    arb_clear(q); arb_clear(t); return 0;
}

/* gamma(eps) = pi / (2 (K_Kr - eps)), K_Kr = pi / (2 asinh 1) */
static void gamma_of_eps(arb_t g, const arb_t eps)
{
    arb_t L, K, pi2; arb_init(L); arb_init(K); arb_init(pi2);
    arb_const_pi(pi2, prec); arb_mul_2exp_si(pi2, pi2, -1);
    arb_one(L); arb_asinh(L, L, prec); arb_div(K, pi2, L, prec);
    arb_sub(g, K, eps, prec); arb_div(g, pi2, g, prec);
    arb_clear(L); arb_clear(K); arb_clear(pi2);
}

/* 1: A(g) + tail <= A_N(g^+) + tail(g^+) < 1 certified (=> c* > g);  -1: A_N(g^-) > 1 certified (=> c* < g); 0 undecided */
static int classify(const arb_t g, const arb_t Rp, const arb_t sh, arb_t outU, arb_t outL)
{
    arb_t gh, gl, A, T; arb_init(gh); arb_init(gl); arb_init(A); arb_init(T);
    arb_get_ubound_arf(arb_midref(gh), g, prec); mag_zero(arb_radref(gh));
    arb_get_lbound_arf(arb_midref(gl), g, prec); mag_zero(arb_radref(gl));
    int res = 0;
    A_N(A, gh);
    if (tail_b(T, gh, Rp, sh) == 0) { arb_add(A, A, T, prec); arb_sub_ui(A, A, 1, prec); if (outU) arb_set(outU, A); if (arb_is_negative(A)) res = 1; }
    A_N(A, gl); arb_sub_ui(A, A, 1, prec); if (outL) arb_set(outL, A);
    if (res == 0 && arb_is_positive(A)) res = -1;
    arb_clear(gh); arb_clear(gl); arb_clear(A); arb_clear(T);
    return res;
}

int main(int argc, char **argv)
{
    setvbuf(stdout, NULL, _IONBF, 0);
    if (argc < 9) { fprintf(stderr, "usage: certify alphaA alphaB N prec J s rho' M' [eps]\n"); return 2; }
    N = atol(argv[3]); prec = atol(argv[4]);
    slong M = N + 1, J = atol(argv[5]);
    const char *sstr = argv[6], *rstr = argv[7], *Mstr = argv[8], *estr = argc > 9 ? argv[9] : "3e-5";
    if (J > N) { fprintf(stderr, "need J <= N\n"); return 2; }

    arb_ptr Af = _arb_vec_init(M * M), Ag = _arb_vec_init(M * M);
    load(Af, M, argv[1]); load(Ag, M, argv[2]);
    arb_ptr C = _arb_vec_init(M), Sf = _arb_vec_init(M), Sg = _arb_vec_init(M);
    arb_t pi2; arb_init(pi2); arb_const_pi(pi2, prec); arb_mul_2exp_si(pi2, pi2, -1);
    for (slong k = 0; k <= N; k++)
    {
        for (slong m = 0; m <= k; m++)
        {
            arb_addmul(C + k, Af + m * M + (k - m), Ag + m * M + (k - m), prec);
            arb_addmul(Sf + k, Af + m * M + (k - m), Af + m * M + (k - m), prec);
            arb_addmul(Sg + k, Ag + m * M + (k - m), Ag + m * M + (k - m), prec);
        }
        arb_mul(C + k, C + k, pi2, prec);
    }
    printf("== Coefficients of H (N = %ld, prec = %ld)\n", N, prec);
    printf("C_1   = "); arb_printn(C + 1, 25, 0); printf("\nC_3   = "); arb_printn(C + 3, 25, 0);
    printf("\nC_5   = "); arb_printn(C + 5, 25, 0); printf("\nC_%ld = ", N - 1 + (N % 2)); arb_printn(C + N - 1 + (N % 2), 15, 0); printf("\n");
    { int evenzero = 1; for (slong k = 0; k <= N; k += 2) if (!arb_is_zero(C + k)) evenzero = 0; printf("even C_k identically zero: %s\n", evenzero ? "yes" : "NO"); }
    arb_t Pf, Pg; arb_init(Pf); arb_init(Pg);
    for (slong k = 0; k <= N; k++) { arb_add(Pf, Pf, Sf + k, prec); arb_add(Pg, Pg, Sg + k, prec); }
    printf("sum_{k<=N} S^f_k = "); arb_printn(Pf, 20, 0); printf("\nsum_{k<=N} S^g_k = "); arb_printn(Pg, 20, 0); printf("\n");

    /* compositional inverse */
    arb_poly_t H; arb_poly_init(H); arb_poly_init(B);
    for (slong k = 0; k <= N; k++) arb_poly_set_coeff_arb(H, k, C + k);
    arb_poly_revert_series(B, H, N + 1, prec);
    { arb_t x; arb_init(x);
      for (slong n = 1; n <= 7; n += 2) { arb_poly_get_coeff_arb(x, B, n); printf("b_%ld   = ", n); arb_printn(x, 20, 0); printf("\n"); }
      arb_poly_get_coeff_arb(x, B, N - 1 + (N % 2)); printf("b_%ld = ", N - 1 + (N % 2)); arb_printn(x, 10, 0); printf("\n");
      double maxrad = 0; slong nr = 0;
      for (slong n = 1; n <= N; n++) { arb_poly_get_coeff_arb(x, B, n); double r = mag_get_d(arb_radref(x)); if (r > maxrad) { maxrad = r; nr = n; } }
      printf("max radius of b_n (n <= N): %.3e at n = %ld\n", maxrad, nr); arb_clear(x); }

    /* ---------- phi = E o sin ---------- */
    printf("\n== Rouche tail: s = %s, rho' = %s, M' = %s, J = %ld\n", sstr, rstr, Mstr, J);
    arb_poly_t Ep, Sp, Ph, X; arb_poly_init(Ep); arb_poly_init(Sp); arb_poly_init(Ph); arb_poly_init(X);
    arb_t ak; arb_init(ak);
    for (slong k = 1; k <= J; k += 2)
    {
        slong mm = (k - 1) / 2; fmpz_t bn; fmpz_init(bn); fmpz_bin_uiui(bn, 2 * mm, mm);
        arb_set_fmpz(ak, bn); arb_mul_2exp_si(ak, ak, -2 * mm); arb_div_ui(ak, ak, k, prec); fmpz_clear(bn);
        arb_sub(ak, C + k, ak, prec); arb_poly_set_coeff_arb(Ep, k, ak);
    }
    arb_poly_set_coeff_si(X, 1, 1);
    arb_poly_sin_series(Sp, X, J + 1, prec);
    arb_poly_compose_series(Ph, Ep, Sp, J + 1, prec);
    printf("phi_1 = "); arb_printn(arb_poly_get_coeff_ptr(Ph, 1), 15, 0);
    printf("\nphi_3 = "); arb_printn(arb_poly_get_coeff_ptr(Ph, 3), 15, 0); printf("\n");

    arb_t sv, rp, Mp, rad, th, pi; arb_init(sv); arb_init(rp); arb_init(Mp); arb_init(rad); arb_init(th); arb_init(pi);
    arb_set_str(sv, sstr, prec); arb_set_str(rp, rstr, prec); arb_set_str(Mp, Mstr, prec); arb_const_pi(pi, prec);
    /* sup over |zeta| = s, theta in [0, pi/2] (phi odd, real coefficients), K arcs */
    slong K = 4000;
    mag_t mx, mg, dsum, rr, pw, tmg, smag, dev; mag_init(mx); mag_init(mg); mag_init(dsum); mag_init(rr); mag_init(pw); mag_init(tmg); mag_init(smag); mag_init(dev);
    arb_div_ui(rad, pi, 4 * K, prec); arb_mul(rad, rad, sv, prec); arb_get_mag(rr, rad);   /* |zeta - zeta_mid| <= s pi/(4K) */
    { arb_t sr; arb_init(sr); arb_add(sr, sv, rad, prec); arb_get_mag(smag, sr); arb_clear(sr); }
    mag_one(pw);
    for (slong j = 1; j < arb_poly_length(Ph); j++)
    { arb_get_mag(tmg, arb_poly_get_coeff_ptr(Ph, j)); mag_mul_ui(tmg, tmg, j); mag_mul(tmg, tmg, pw); mag_add(dsum, dsum, tmg); mag_mul(pw, pw, smag); }
    mag_mul(dev, dsum, rr);
    printf("arc deviation bound r * sup|P'| <= "); mag_printd(dev, 4); printf("\n");
    acb_t zt, val; acb_init(zt); acb_init(val);
    for (slong j = 0; j < K; j++)
    {
        arb_mul_ui(th, pi, 2 * j + 1, prec); arb_div_ui(th, th, 4 * K, prec);
        acb_set_arb(zt, th); acb_mul_onei(zt, zt); acb_exp(zt, zt, prec); acb_mul_arb(zt, zt, sv, prec);
        eval_poly(val, Ph, zt);
        acb_get_mag(mg, val); mag_add(mg, mg, dev); mag_max(mx, mx, mg);
    }
    printf("sup_{|zeta|=s} |sum_{j<=J} phi_j zeta^j| <= "); mag_printd(mx, 8); printf("\n");

    if (argc > 10)
    {
        FILE *fo = fopen(argv[10], "w"); arb_t x; arb_init(x); char lab[64];
        fprintf(fo, "# N %ld J %ld s %s rho %s M %s prec %ld\n", N, J, sstr, rstr, Mstr, prec);
        arf_set_mag(arb_midref(x), mx); mag_zero(arb_radref(x)); put_up(fo, "Psup", x, 15);
        for (slong n = 1; n <= N; n += 2)
        {
            arb_poly_get_coeff_arb(x, B, n); arb_abs(x, x);
            sprintf(lab, "bU %ld", n); put_up(fo, lab, x, 40);
            sprintf(lab, "bL %ld", n); put_lo(fo, lab, x, 40);
        }
        fclose(fo); arb_clear(x);
    }
    /* delta = poly sup + M' (s/rho')^{J+1}/(1 - s/rho') */
    arb_t r, tl, delta, Rp, sh, one, t; arb_init(r); arb_init(tl); arb_init(delta); arb_init(Rp); arb_init(sh); arb_init(one); arb_init(t);
    arb_div(r, sv, rp, prec); arb_pow_ui(tl, r, J + 1, prec); arb_sub_ui(t, r, 1, prec); arb_neg(t, t);
    arb_div(tl, tl, t, prec); arb_mul(tl, tl, Mp, prec);
    printf("Taylor tail of phi beyond J: M' (s/rho')^{J+1}/(1-s/rho') = "); arb_printn(tl, 8, 0); printf("\n");
    { arb_t mxa; arb_init(mxa); arf_set_mag(arb_midref(mxa), mx); arb_add(delta, mxa, tl, prec); arb_clear(mxa); }
    { arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, delta, prec); arb_set_arf(delta, ub); arf_clear(ub); }
    printf("delta (upper bound) = "); arf_printd(arb_midref(delta), 10); printf("\n");
    /* R' = s - delta - 1e-10 (exact lower point) */
    arb_sub(Rp, sv, delta, prec); arb_set_str(t, "1e-10", prec); arb_sub(Rp, Rp, t, prec);
    { arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, Rp, prec); arb_set_arf(Rp, lb); arf_clear(lb); }
    printf("R' = s - delta - 1e-10 = "); arf_printd(arb_midref(Rp), 12); printf("  (H^{-1} analytic on |w| < R' + 1e-10, |H^{-1}| <= sinh s)\n");
    arb_sinh(sh, sv, prec); printf("sinh(s) = "); arb_printn(sh, 12, 0); printf("\n");

    /* ---------- the target eps ---------- */
    arb_t eps, g, A, T; arb_init(eps); arb_init(g); arb_init(A); arb_init(T);
    arb_set_str(eps, estr, prec); gamma_of_eps(g, eps);
    { arb_t L, Kk; arb_init(L); arb_init(Kk); arb_one(L); arb_asinh(L, L, prec); arb_div(Kk, pi2, L, prec);
      printf("\n== Target eps = %s\nK_Kr = pi/(2 asinh 1) = ", estr); arb_printn(Kk, 22, 0); arb_clear(L); arb_clear(Kk); }
    printf("\ngamma_t = pi/(2(K_Kr - eps)) = "); arb_printn(g, 22, 0); printf("\n");
    arb_t gh; arb_init(gh); arb_get_ubound_arf(arb_midref(gh), g, prec);
    A_N(A, gh); printf("A_N(gamma_t^+) = "); arb_printn(A, 22, 0); printf("\n");
    if (tail_b(T, gh, Rp, sh)) { printf("q >= 1: no tail bound\n"); return 1; }
    printf("q = gamma_t^+/R' = "); { arb_t q; arb_init(q); arb_div(q, gh, Rp, prec); arb_printn(q, 12, 0); arb_clear(q); }
    printf("\ntail sum_{n>N} |b_n| gamma_t^n <= sinh(s) q^{N+1}/(1-q) = "); arb_printn(T, 8, 0); printf("\n");
    arb_add(A, A, T, prec); arb_sub_ui(A, A, 1, prec);
    { arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, A, prec); printf("A(gamma_t) - 1 <= A_N(gamma_t^+) + tail - 1 <= "); arf_printd(ub, 15); printf("\n"); arf_clear(ub); }
    int ok = arb_is_negative(A);
    printf("CERTIFIED A(gamma_t) < 1, hence K_G <= pi/(2 gamma_t) = K_Kr - %s : %s\n", estr, ok ? "YES" : "NO");
    /* existence of the root c*: A_N(0.9) > 1 and 0.9 < R' */
    arb_set_str(t, "0.9", prec); A_N(A, t); arb_sub_ui(A, A, 1, prec);
    printf("A_N(0.9) - 1 = "); arb_printn(A, 12, 0); printf("   0.9 < R': %s\n", arb_lt(t, Rp) ? "yes" : "NO");

    /* ---------- two-sided enclosure of c* (A(c*) = 1) and of the best eps ---------- */
    printf("\n== Enclosure of the root c* of A(c) = 1\n");
    arb_t glo, ghi, gm, outU, outL; arb_init(glo); arb_init(ghi); arb_init(gm); arb_init(outU); arb_init(outL);
    arb_set_str(glo, "0.8813", prec); arb_set_str(ghi, "0.8815", prec);
    if (classify(glo, Rp, sh, NULL, NULL) != 1 || classify(ghi, Rp, sh, NULL, NULL) != -1) { printf("bracket failure\n"); return 1; }
    for (int it = 0; it < 60; it++)
    {
        arb_add(gm, glo, ghi, prec); arb_mul_2exp_si(gm, gm, -1);
        { arf_t m; arf_init(m); arf_set_round(m, arb_midref(gm), 64, ARF_RND_DOWN); arb_set_arf(gm, m); arf_clear(m); }
        int c = classify(gm, Rp, sh, outU, outL);
        if (c == 1) arb_set(glo, gm); else if (c == -1) arb_set(ghi, gm); else { printf("undecided at gamma = "); arb_printn(gm, 20, 0); printf("\n"); break; }
    }
    classify(glo, Rp, sh, outU, NULL); printf("gamma_lo = "); arb_printn(glo, 20, 0); printf("   A_N + tail - 1 <= "); arb_printn(outU, 6, 0); printf("\n");
    classify(ghi, Rp, sh, NULL, outL); printf("gamma_hi = "); arb_printn(ghi, 20, 0); printf("   A_N - 1 >= "); arb_printn(outL, 6, 0); printf("\n");
    /* eps(gamma) = K_Kr - pi/(2 gamma) */
    { arb_t L, Kk, e1, e2; arb_init(L); arb_init(Kk); arb_init(e1); arb_init(e2);
      arb_one(L); arb_asinh(L, L, prec); arb_div(Kk, pi2, L, prec);
      arb_div(e1, pi2, glo, prec); arb_sub(e1, Kk, e1, prec);
      arb_div(e2, pi2, ghi, prec); arb_sub(e2, Kk, e2, prec);
      printf("certified: K_G <= pi/(2 gamma_lo) = K_Kr - eps_lo, eps_lo = "); arb_printn(e1, 15, 0);
      printf("\nthese profiles cannot give more than eps_hi = "); arb_printn(e2, 15, 0);
      arb_div(e1, pi2, glo, prec); printf("\nupper bound for K_G: "); arb_printn(e1, 20, 0); printf("\n");
      arb_clear(L); arb_clear(Kk); arb_clear(e1); arb_clear(e2); }
    return ok ? 0 : 1;
}
