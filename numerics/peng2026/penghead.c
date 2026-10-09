/*
  penghead.c -- independent enclosure of the coefficient head of the correlation function of
  Bo Peng's scheme (arXiv:2609.20074v1): threshold P of degree 11, signed correlation rho of degree 51.

  With alpha_{m,n} = int psi_m(u) I_n(a(u)) dmu(u) from alpha.c (m = degree in the x-coordinate,
  n = degree in the threshold coordinate w), the scheme f(w,x) = sgn(w + P(x)),
  g(w,x) = f(w,-x), with corr(W,W') = rho(t) and corr(X,X') = t, has, by Mehler's formula in each
  of the two independent coordinate pairs and alpha^g_{m,n} = (-1)^m alpha^f_{m,n},

      H(t) = (pi/2) E[f g] = (pi/2) sum_{m,n} (-1)^m alpha_{m,n}^2 t^m rho(t)^n,
      rho(t) = sum_j c_j t^j  (exact decimals from a file; ||rho||_A < 1 is checked).

  [t^k] of the n-th term vanishes unless m + n <= k, so b_k for k <= N needs alpha_{m,n}, m + n <= N only.
  Output: b_1, b_3, b_5, lower bound of b_1, upper bound of sum_{3<=k<=N, k odd} |b_k|, the Parseval
  sum, and (sanity check) the partial inverse majorant sum_{n<=N} |a_n| gamma^n.

  usage: penghead alpha_file N prec rho_file   (gamma = 5000 pi / 17813)
*/
#include <stdio.h>
#include <stdlib.h>
#include <flint/arb.h>
#include <flint/arb_poly.h>

int main(int argc, char **argv)
{
    if (argc < 5) { fprintf(stderr, "usage: penghead alpha_file N prec rho_file\n"); return 2; }
    slong N = atol(argv[2]), prec = atol(argv[3]), M = N + 1;
    arb_ptr A = _arb_vec_init(M * M);
    { FILE *f = fopen(argv[1], "r"); long m, n; static char buf[100000];
      if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 1; }
      while (fscanf(f, "%ld %ld %99999[^\n]", &m, &n, buf) == 3)
          if (m <= N && n <= N && m + n <= N) { if (arb_load_str(A + m * M + n, buf)) { fprintf(stderr, "load error\n"); return 1; } }
      fclose(f); }
    arb_t x, pi2, gam, RA; arb_init(x); arb_init(pi2); arb_init(gam); arb_init(RA);
    arb_const_pi(pi2, prec); arb_mul_2exp_si(pi2, pi2, -1);
    arb_const_pi(gam, prec); arb_mul_ui(gam, gam, 5000, prec); arb_div_ui(gam, gam, 17813, prec);
    arb_poly_t rho, rn, P, T, H; arb_poly_init(rho); arb_poly_init(rn); arb_poly_init(P); arb_poly_init(T); arb_poly_init(H);
    { FILE *f = fopen(argv[4], "r"); long j; char buf[128];
      while (fscanf(f, "%ld %127s", &j, buf) == 2) { if (arb_set_str(x, buf, prec)) { fprintf(stderr, "bad %s\n", buf); return 1; } arb_poly_set_coeff_arb(rho, j, x); arb_abs(x, x); arb_add(RA, RA, x, prec); }
      fclose(f); }
    printf("||rho||_A = "); arb_printn(RA, 30, 0); printf("\n");

    /* Parseval: sum alpha^2 over m + n <= N (must be <= 1) */
    arb_t pars; arb_init(pars);
    for (slong i = 0; i < M * M; i++) arb_addmul(pars, A + i, A + i, prec);

    arb_poly_one(rn);
    for (slong n = 0; n <= N; n++)
    {
        /* P(t) = sum_{m <= N-n} (-1)^m alpha_{m,n}^2 t^m */
        arb_poly_zero(P);
        for (slong m = 0; m + n <= N; m++)
        {
            arb_sqr(x, A + m * M + n, prec); if (m & 1) arb_neg(x, x);
            if (!arb_is_zero(x)) arb_poly_set_coeff_arb(P, m, x);
        }
        arb_poly_mullow(T, P, rn, N + 1, prec);
        arb_poly_add(H, H, T, prec);
        arb_poly_mullow(rn, rn, rho, N + 1, prec);
    }
    arb_poly_scalar_mul(H, H, pi2, prec);

    printf("Peng scheme, rho from %s, N = %ld, prec = %ld\n", argv[4], N, prec); printf("gamma = 5000 pi/17813 = "); arb_printn(gam, 20, 0); printf("\n");
    printf("Parseval sum_{m+n<=N} alpha^2 = "); arb_printn(pars, 20, 0); printf("\n");
    for (slong k = 0; k <= 7; k++) { arb_poly_get_coeff_arb(x, H, k); printf("b_%ld = ", k); arb_printn(x, 22, 0); printf("\n"); }
    { int ev = 1; for (slong k = 0; k <= N; k += 2) { arb_poly_get_coeff_arb(x, H, k); if (!arb_contains_zero(x)) ev = 0; } printf("even coefficients contain 0: %s\n", ev ? "yes" : "NO"); }
    arf_t lb, ub; arf_init(lb); arf_init(ub);
    arb_poly_get_coeff_arb(x, H, 1); arb_get_lbound_arf(lb, x, prec);
    printf("b_1 >= "); arf_printd(lb, 15); printf("\n");
    arb_t S; arb_init(S);
    double rmax = 0;
    for (slong k = 3; k <= N; k += 2) { arb_poly_get_coeff_arb(x, H, k); arb_abs(x, x); arb_add(S, S, x, prec); double r = mag_get_d(arb_radref(x)); if (r > rmax) rmax = r; }
    arb_get_ubound_arf(ub, S, prec);
    printf("sum_{3<=k<=%ld, k odd} |b_k| = ", N); arb_printn(S, 15, 0); printf("  <= "); arf_printd(ub, 12); printf("   (max radius of b_k: %.3e)\n", rmax);
    for (slong k = 9; k <= N; k += 40) { arb_poly_get_coeff_arb(x, H, k); printf("  b_%ld = ", k); arb_printn(x, 8, 0); printf("\n"); }
    /* margin of the near-linearity criterion without the tail */
    arb_poly_get_coeff_arb(x, H, 1); arb_sub(x, x, gam, prec); arb_sub(x, x, S, prec);
    printf("b_1 - gamma - head = "); arb_printn(x, 12, 0); printf("   (room left for the tail sum_{k>%ld} |b_k|)\n", N);

    /* sanity: inverse series and partial inverse majorant at gamma */
    arb_poly_t B; arb_poly_init(B); arb_poly_revert_series(B, H, N + 1, prec);
    arb_t Ms, gp; arb_init(Ms); arb_init(gp); arb_one(gp);
    for (slong n = 1; n <= N; n++) { arb_mul(gp, gp, gam, prec); arb_poly_get_coeff_arb(x, B, n); arb_abs(x, x); arb_mul(x, x, gp, prec); arb_add(Ms, Ms, x, prec); }
    for (slong n = 1; n <= 7; n += 2) { arb_poly_get_coeff_arb(x, B, n); printf("a_%ld = ", n); arb_printn(x, 15, 0); printf("\n"); }
    printf("partial inverse majorant sum_{n<=%ld} |a_n| gamma^n = ", N); arb_printn(Ms, 15, 0); printf("\n");
    arb_poly_get_coeff_arb(x, B, N); printf("a_%ld = ", N); arb_printn(x, 6, 0); printf("\n");
    return 0;
}
