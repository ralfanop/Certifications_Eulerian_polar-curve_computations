/*
  mbound.c -- profile-independent rigorous bound  M' >= sup_{|zeta| = rho'} |E(sin zeta)|,  E = H - arcsin.

  For any odd profiles a, b (f = sign(x2 - a(x1)), g = sign(x2 - b(x1))) and z in the star-shaped
  set where the margin m(t) = Re w_t - |Re(t w_t)|, w_t = 1/(1 - t^2), is positive along [0, z]:

     E(z) = (pi/2) int int p_z(u,v) D(a(u), b(v); z) du dv,
     p_z(u,v) = exp(-Q_z(u,v)) / (pi sqrt(1 - z^2)),  Re Q_z(u,v) >= m(z) (u^2 + v^2),
     D(a,b;z) = erf(a) erf(b) + 2 int_0^z [p_t(a,b) - p_t(0,0)] dt,  |p_t(a,b)| <= 1/(pi |1 - t^2|^{1/2}).

  Hence
     |E(z)| <= (pi/2) * |1 - z^2|^{-1/2} / m(z) * (1 + (4 |z| / pi) * sup_{t in [0,z]} |1 - t^2|^{-1/2}).

  Everything below is ball arithmetic (Arb).  theta in [0, pi/2] suffices (E o sin is odd with real
  coefficients).  The program also certifies, on |zeta| = rho':
     (i)   |Re sin zeta| < 1   (so sin(closed disk) avoids the cuts (-inf,-1], [1,inf)),
     (ii)  m(t) > 0 on every segment [0, sin zeta]  (by starlikeness these segments cover sin(closed disk)),
     (iii) rho' cot rho' > 0, which gives Re(zeta cot zeta) >= rho' cot rho' > 0 on |zeta| = rho'
           (z cot z = 1 - 2 sum zeta(2k) (z/pi)^{2k}), i.e. sin(disk) is starlike w.r.t. 0.

  usage: mbound rho' K NSEG prec
*/
#include <stdio.h>
#include <stdlib.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/fmpz.h>

int main(int argc, char **argv)
{
    if (argc < 5) { fprintf(stderr, "usage: mbound rho' K NSEG prec\n"); return 2; }
    const char *rhos = argv[1]; slong K = atol(argv[2]), NSEG = atol(argv[3]), prec = atol(argv[4]);
    arb_t rho, th, rad, x, y, tmp, mz, mt, inv, Ms, Mmax, pi, one_r, lam, zabs, ReMax, MinMarg, fac;
    arb_init(rho); arb_init(th); arb_init(rad); arb_init(x); arb_init(y); arb_init(tmp); arb_init(mz); arb_init(mt);
    arb_init(inv); arb_init(Ms); arb_init(Mmax); arb_init(pi); arb_init(one_r); arb_init(lam); arb_init(zabs);
    arb_init(ReMax); arb_init(MinMarg); arb_init(fac);
    acb_t zeta, z, t, w, tw, one; acb_init(zeta); acb_init(z); acb_init(t); acb_init(w); acb_init(tw); acb_init(one);
    arb_set_str(rho, rhos, prec); arb_const_pi(pi, prec); acb_one(one);

    /* (iii) starlikeness: rho' cot rho' > 0 */
    arb_cot(tmp, rho, prec); arb_mul(tmp, tmp, rho, prec);
    printf("rho' cot rho' = "); arb_printn(tmp, 12, 0); printf("  (> 0: %s)\n", arb_is_positive(tmp) ? "yes" : "NO");
    if (!arb_is_positive(tmp)) return 1;

    arb_zero(Mmax); arb_zero(ReMax); arb_set_ui(MinMarg, 1000);
    for (slong j = 0; j < K; j++)
    {
        /* theta ball covering [pi/2 * j/K, pi/2 * (j+1)/K] */
        arb_mul_ui(th, pi, 2 * j + 1, prec); arb_div_ui(th, th, 4 * K, prec);
        arb_div_ui(rad, pi, 4 * K, prec); arb_add_error(th, rad);
        arb_sin_cos(y, x, th, prec); arb_mul(x, x, rho, prec); arb_mul(y, y, rho, prec);
        acb_set_arb_arb(zeta, x, y);
        acb_sin(z, zeta, prec);
        /* (i) |Re z| < 1 */
        arb_abs(tmp, acb_realref(z)); { arb_t ub; arb_init(ub); arb_get_ubound_arf(arb_midref(ub), tmp, prec); if (arf_cmp(arb_midref(ub), arb_midref(ReMax)) > 0) arf_set(arb_midref(ReMax), arb_midref(ub)); arb_clear(ub); }
        arb_sub_ui(tmp, tmp, 1, prec); if (!arb_is_negative(tmp)) { printf("strip failure at arc %ld\n", j); return 1; }

        /* sup over the segment [0, z] of |1 - t^2|^{-1/2}, and margin positivity */
        arb_zero(Ms);
        for (slong q = 0; q < NSEG; q++)
        {
            arb_set_ui(lam, 2 * q + 1); arb_div_ui(lam, lam, 2 * NSEG, prec);
            arb_one(rad); arb_div_ui(rad, rad, 2 * NSEG, prec); arb_add_error(lam, rad);
            acb_mul_arb(t, z, lam, prec);
            acb_sqr(w, t, prec); acb_sub(w, one, w, prec);           /* 1 - t^2 */
            acb_abs(tmp, w, prec); arb_rsqrt(inv, tmp, prec);         /* |1 - t^2|^{-1/2} */
            if (!arb_is_finite(inv)) { printf("|1-t^2| not bounded below at arc %ld seg %ld\n", j, q); return 1; }
            arb_union(Ms, Ms, inv, prec);
            acb_inv(w, w, prec); acb_mul(tw, t, w, prec);
            arb_abs(tmp, acb_realref(tw)); arb_sub(mt, acb_realref(w), tmp, prec);
            if (!arb_is_positive(mt)) { printf("margin failure at arc %ld seg %ld: ", j, q); arb_printn(mt, 6, 0); printf("\n"); return 1; }
            { arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, mt, prec); if (arf_cmp(lb, arb_midref(MinMarg)) < 0) arf_set(arb_midref(MinMarg), lb); arf_clear(lb); }
        }
        /* at z itself */
        acb_sqr(w, z, prec); acb_sub(w, one, w, prec);
        acb_abs(tmp, w, prec); arb_rsqrt(inv, tmp, prec);
        acb_inv(w, w, prec); acb_mul(tw, z, w, prec);
        arb_abs(tmp, acb_realref(tw)); arb_sub(mz, acb_realref(w), tmp, prec);
        if (!arb_is_positive(mz)) { printf("endpoint margin failure at arc %ld\n", j); return 1; }
        acb_abs(zabs, z, prec);
        /* bound = (pi/2) * inv / mz * (1 + 4 |z| Ms / pi) */
        arb_mul(fac, zabs, Ms, prec); arb_mul_ui(fac, fac, 4, prec); arb_div(fac, fac, pi, prec); arb_add_ui(fac, fac, 1, prec);
        arb_mul(fac, fac, inv, prec); arb_div(fac, fac, mz, prec); arb_mul(fac, fac, pi, prec); arb_mul_2exp_si(fac, fac, -1);
        arb_union(Mmax, Mmax, fac, prec);
        if (j % (K / 10) == 0) { printf("arc %5ld  |z| ", j); arb_printn(zabs, 6, 0); printf("  m(z) "); arb_printn(mz, 6, 0); printf("  sup|1-t^2|^-1/2 "); arb_printn(Ms, 6, 0); printf("  bound "); arb_printn(fac, 6, 0); printf("\n"); }
    }
    { arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, Mmax, prec);
      printf("rho' = %s, K = %ld, NSEG = %ld\n", rhos, K, NSEG);
      printf("max |Re sin zeta| <= "); arf_printd(arb_midref(ReMax), 10); printf("\n");
      printf("min margin on the segments >= "); arf_printd(arb_midref(MinMarg), 10); printf("\n");
      printf("M' (upper bound of sup_{|zeta|=rho'} |E(sin zeta)|) = "); arf_printd(ub, 12); printf("\n");
      { fmpz_t m; fmpz_init(m); arf_mul_2exp_si(ub, ub, 0); arb_t y; arb_init(y); arb_set_arf(y, ub); arb_mul_ui(y, y, 10000000000UL, prec);
        arf_get_fmpz(m, arb_midref(y), ARF_RND_CEIL); printf("M'_up_1e-10 "); fmpz_print(m); printf("   (exact: M' <= this * 10^-10)\n"); fmpz_clear(m); arb_clear(y); }
      arf_clear(ub); }
    return 0;
}
