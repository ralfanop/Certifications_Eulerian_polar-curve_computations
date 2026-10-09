/*
  alpha.c -- rigorous Hermite coefficients of f(x1,x2) = sign(x2 - a(x1)).

  a(u) = sum_j A_j h_{2j+1}(u), h_n = pi^{-1/4} psi_n, psi_n = H_n / sqrt(2^n n!),
  with the 51 coefficients A_j read verbatim (decimal strings) from a profile file.
  With dmu(x) = e^{-x^2} dx / sqrt(pi),

      alpha_{m,n} = int psi_m(u) I_n(a(u)) dmu(u),
      I_0(a) = -erf(a),   I_n(a) = sqrt(2/(pi n)) e^{-a^2} psi_{n-1}(a)  (n >= 1).

  f is odd, so alpha_{m,n} = 0 when m+n is even, and for m+n odd the integrand
  is even in u: alpha_{m,n} = 2 int_0^infinity.

  Method (all in Arb ball arithmetic):
   * [0, U] is cut into nsub subintervals [c-h, c+h], c = (2s+1)/20, h = 1/20 (Arb balls
     enclosing the exact rationals, so the subintervals tile [0, U], U = nsub/10, exactly; default nsub = 45); on each, P = 60 point
     Gauss-Legendre (rigorous nodes and weights from arb_hypgeom_legendre_p_ui_root).
   * Quadrature error on each subinterval: for F analytic in the Bernstein ellipse
     E_rho with |F| <= M there, the P-point rule satisfies
         |int - Q_P| <= h (64/15) M rho^{-(2P-2)} / (rho^2 - 1)
     (Trefethen, Approximation Theory and Approximation Practice, Thm 19.3, stated there
     for n + 1 = P points).  M is bounded by sup_{E_rho} |psi_m(u) e^{-u^2}| * sup_{E_rho} |I_n(a(u))|,
     both computed on balls covering the ellipse boundary (maximum modulus principle), with a
     midpoint-plus-Taylor-deviation bound for psi_m and a(u).  rho in {1.25, 1.6, 2.2, 3.5};
     the smallest bound is kept, per (m,n) and subinterval.
   * Outer region [U, U2], U2 = U + 4.5: 72 cells of width 1/16 (exact doubles), bisected until either
     |a| >= 15 on the whole cell (then I_0 = -sign(a) (1 - erfc|a|) and |I_n| <= e^{-112} for n >= 1, so
     only alpha_{m,0} gets the main term -sign(a) (2/sqrt(pi)) int psi_m e^{-u^2}, by Gauss-Legendre with
     an ellipse (rho = 3) error bound, plus erfc(15) and e^{-112} radii), or the cell is a "root cell"
     of width < 2e-8 (then |I_n| <= 1 and the whole contribution goes into the radius).
     Ball centres and radii of real cells are formed exactly from the double endpoints.
   * Tail u > U2:  |psi_m(u)| e^{-u^2/2} <= 1.0865 (Cramer's inequality) and
     |I_n| <= 1, hence |2 int_U2^inf| <= (2/sqrt(pi)) 1.0865 sqrt(pi/2) erfc(U2/sqrt2).

  Output: one line per (m,n) with m+n odd, m+n <= N0:  "m n <arb_dump_str>".
  usage: alpha profile.txt N0 prec out.txt
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/arb_mat.h>
#include <flint/arb_hypgeom.h>
#include <flint/acb_hypgeom.h>

#define NMODES 51
#define MAXDEG 101

static slong prec;
static arb_t Acoef[NMODES];   /* A_j * pi^{-1/4} */
static arb_ptr sq_a, sq_b;    /* sqrt(2/(n+1)), sqrt(n/(n+1)) for recurrence */
static arb_ptr In_c;          /* sqrt(2/(pi n)) */
static slong NMAX;

static void psi_vec(acb_ptr out, const acb_t x, slong nmax)
{
    acb_one(out);
    if (nmax >= 1) { acb_mul_arb(out + 1, x, sq_a + 0, prec); }
    for (slong n = 1; n < nmax; n++)
    {
        acb_t t; acb_init(t);
        acb_mul(t, x, out + n, prec);
        acb_mul_arb(t, t, sq_a + n, prec);
        acb_submul_arb(t, out + n - 1, sq_b + n, prec);
        acb_swap(out + n + 1, t);
        acb_clear(t);
    }
}

static void profile(acb_t a, const acb_t u)
{
    acb_ptr p = _acb_vec_init(MAXDEG + 1);
    psi_vec(p, u, MAXDEG);
    acb_zero(a);
    for (int j = 0; j < NMODES; j++) acb_addmul_arb(a, p + 2 * j + 1, Acoef[j], prec);
    _acb_vec_clear(p, MAXDEG + 1);
}

/* I_n(a) for n = 0..N */
static void I_vec(acb_ptr out, const acb_t a, slong N)
{
    acb_t t, e; acb_init(t); acb_init(e);
    acb_hypgeom_erf(out, a, prec); acb_neg(out, out);
    acb_ptr p = _acb_vec_init(N + 1);
    psi_vec(p, a, N);
    acb_mul(t, a, a, prec); acb_neg(t, t); acb_exp(e, t, prec);
    for (slong n = 1; n <= N; n++)
    {
        acb_mul(out + n, p + n - 1, e, prec);
        acb_mul_arb(out + n, out + n, In_c + n, prec);
    }
    _acb_vec_clear(p, N + 1);
    acb_clear(t); acb_clear(e);
}

/* Upper bounds on a ball B(c0, r) (c0 exact complex midpoint, r >= 0):
   sup_B |psi_m| <= |psi_m(c0)| + Mpsi_m (e^{r sqrt(2m)} - 1),  Mpsi_m = max_{k<=m} |psi_k(c0)|,
   from the exact Taylor expansion psi_m^{(j)} = sqrt(2^j m!/(m-j)!) psi_{m-j}. */
static void psi_sup_ball(mag_ptr out, const acb_t c0, const mag_t r, slong N)
{
    acb_ptr p = _acb_vec_init(N + 1);
    psi_vec(p, c0, N);
    mag_t Mx, cur, e, t; mag_init(Mx); mag_init(cur); mag_init(e); mag_init(t);
    arb_t q; arb_init(q);
    mag_zero(Mx);
    for (slong m = 0; m <= N; m++)
    {
        acb_get_mag(cur, p + m);
        mag_max(Mx, Mx, cur);
        /* e = exp(r sqrt(2m)) - 1 */
        mag_set_ui(t, 2 * m); mag_sqrt(t, t); mag_mul(t, t, r); mag_expm1(e, t);
        mag_mul(e, e, Mx);
        mag_add(out + m, cur, e);
    }
    _acb_vec_clear(p, N + 1);
    mag_clear(Mx); mag_clear(cur); mag_clear(e); mag_clear(t); arb_clear(q);
}

/* For the ball B(c0,r): Pm[m] = sup |psi_m(u) e^{-u^2}|, Qn[n] = sup |I_n(a(u))| (maxed into). */
static void ball_bounds(mag_ptr Pm, mag_ptr Qn, const acb_t c0, const mag_t r, slong N0)
{
    mag_ptr ps = _mag_vec_init(MAXDEG + 1 > N0 + 1 ? MAXDEG + 1 : N0 + 1);
    slong L = (MAXDEG > N0 ? MAXDEG : N0);
    psi_sup_ball(ps, c0, r, L);
    acb_t ub, t, a0, ab; acb_init(ub); acb_init(t); acb_init(a0); acb_init(ab);
    mag_t me, mg, ra, tm; mag_init(me); mag_init(mg); mag_init(ra); mag_init(tm);
    /* sup |e^{-u^2}| on the ball */
    acb_set(ub, c0); mag_add(arb_radref(acb_realref(ub)), arb_radref(acb_realref(ub)), r);
    mag_add(arb_radref(acb_imagref(ub)), arb_radref(acb_imagref(ub)), r);
    acb_sqr(t, ub, prec); acb_neg(t, t); acb_exp(t, t, prec); acb_get_mag(me, t);
    for (slong m = 0; m <= N0; m++) { mag_mul(mg, ps + m, me); mag_max(Pm + m, Pm + m, mg); }
    /* a(u): midpoint value and radius ra = pi^{-1/4} sum |A_j| (sup_B|psi_mode| - |psi_mode(c0)|) <= ... */
    acb_ptr p = _acb_vec_init(L + 1);
    psi_vec(p, c0, L);
    acb_zero(a0); mag_zero(ra);
    {
        mag_t Mx, cur, dv; mag_init(Mx); mag_init(cur); mag_init(dv); mag_zero(Mx);
        int j = 0;
        for (slong k = 0; k <= MAXDEG; k++)
        {
            acb_get_mag(cur, p + k); mag_max(Mx, Mx, cur);
            if (k == 2 * j + 1 && j < NMODES)
            {
                acb_addmul_arb(a0, p + k, Acoef[j], prec);
                /* |psi_k(u) - psi_k(c0)| <= Mx (exp(r sqrt(2k)) - 1) */
                mag_set_ui(dv, 2 * k); mag_sqrt(dv, dv); mag_mul(dv, dv, r); mag_expm1(dv, dv); mag_mul(dv, dv, Mx);
                arb_get_mag(tm, Acoef[j]); mag_mul(tm, tm, dv); mag_add(ra, ra, tm);
                j++;
            }
        }
        mag_clear(Mx); mag_clear(cur); mag_clear(dv);
    }
    _acb_vec_clear(p, L + 1);
    (void)ab;
    /* The ball for a: we only know |a(u) - a0| <= sum |A_j| |psi_md(u) - psi_md(c0)| <= ra (crude). */
    acb_set(ab, a0);
    mag_add(arb_radref(acb_realref(ab)), arb_radref(acb_realref(ab)), ra);
    mag_add(arb_radref(acb_imagref(ab)), arb_radref(acb_imagref(ab)), ra);
    /* I_0 */
    acb_hypgeom_erf(t, ab, prec); acb_get_mag(mg, t); mag_max(Qn + 0, Qn + 0, mg);
    if (N0 >= 1)
    {
        mag_ptr pa = _mag_vec_init(N0);
        acb_t amid; acb_init(amid); acb_get_mid(amid, ab);
        mag_t rab; mag_init(rab); mag_hypot(rab, arb_radref(acb_realref(ab)), arb_radref(acb_imagref(ab)));
        psi_sup_ball(pa, amid, rab, N0 - 1);
        acb_sqr(t, ab, prec); acb_neg(t, t); acb_exp(t, t, prec); acb_get_mag(me, t);
        for (slong n = 1; n <= N0; n++)
        {
            arb_get_mag(tm, In_c + n);
            mag_mul(mg, pa + n - 1, me); mag_mul(mg, mg, tm);
            mag_max(Qn + n, Qn + n, mg);
        }
        _mag_vec_clear(pa, N0); acb_clear(amid); mag_clear(rab);
    }
    _mag_vec_clear(ps, (MAXDEG + 1 > N0 + 1 ? MAXDEG + 1 : N0 + 1));
    acb_clear(ub); acb_clear(t); acb_clear(a0); acb_clear(ab);
    mag_clear(me); mag_clear(mg); mag_clear(ra); mag_clear(tm);
}

/* a on the real ball [c0 - r, c0 + r]: midpoint value a0 and deviation bound ra */
static void profile_ball(acb_t a0, mag_t ra, const acb_t c0, const mag_t r)
{
    acb_ptr p = _acb_vec_init(MAXDEG + 1);
    psi_vec(p, c0, MAXDEG);
    acb_zero(a0); mag_zero(ra);
    mag_t Mx, cur, dv, tm; mag_init(Mx); mag_init(cur); mag_init(dv); mag_init(tm); mag_zero(Mx);
    int j = 0;
    for (slong k = 0; k <= MAXDEG; k++)
    {
        acb_get_mag(cur, p + k); mag_max(Mx, Mx, cur);
        if (j < NMODES && k == 2 * j + 1)
        {
            acb_addmul_arb(a0, p + k, Acoef[j], prec);
            mag_set_ui(dv, 2 * k); mag_sqrt(dv, dv); mag_mul(dv, dv, r); mag_expm1(dv, dv); mag_mul(dv, dv, Mx);
            arb_get_mag(tm, Acoef[j]); mag_mul(tm, tm, dv); mag_add(ra, ra, tm);
            j++;
        }
    }
    _acb_vec_clear(p, MAXDEG + 1);
    mag_clear(Mx); mag_clear(cur); mag_clear(dv); mag_clear(tm);
}

/* exact centre (lo+hi)/2 and an upper bound of the half-width (hi-lo)/2 of [lo,hi] (doubles) */
static void exact_cr(acb_t c0, mag_t r, double lo, double hi)
{
    arb_t a, b; arb_init(a); arb_init(b);
    arb_set_d(a, lo); arb_set_d(b, hi);
    arb_add(acb_realref(c0), a, b, 2 * prec); arb_mul_2exp_si(acb_realref(c0), acb_realref(c0), -1); arb_zero(acb_imagref(c0));
    arb_sub(b, b, a, 2 * prec); arb_mul_2exp_si(b, b, -1); arb_get_mag(r, b);
    if (!arb_is_exact(acb_realref(c0))) { fprintf(stderr, "inexact centre\n"); exit(1); }
    arb_clear(a); arb_clear(b);
}

/* S[m] = sup_{u in [lo,hi]} |psi_m(u)| e^{-u^2}, lo >= 0 */
static void psiexp_sup_interval(mag_ptr S, double lo, double hi, slong N)
{
    acb_t c0; acb_init(c0); mag_t r, e; mag_init(r); mag_init(e);
    exact_cr(c0, r, lo, hi);
    psi_sup_ball(S, c0, r, N);
    arb_t x; arb_init(x); arb_set_d(x, lo); arb_sqr(x, x, prec); arb_neg(x, x); arb_exp(x, x, prec); arb_get_mag(e, x);
    for (slong m = 0; m <= N; m++) mag_mul(S + m, S + m, e);
    acb_clear(c0); mag_clear(r); mag_clear(e); arb_clear(x);
}

int main(int argc, char **argv)
{
    if (argc < 5) { fprintf(stderr, "usage: alpha profile|cq:eta:s3:s5 N0 prec out [nsub]\n"); return 1; }
    const char *pf = argv[1]; slong N0 = atol(argv[2]); prec = atol(argv[3]); const char *of = argv[4];
    NMAX = (N0 > MAXDEG ? N0 : MAXDEG) + 2;
    const slong P = 60;              /* Gauss-Legendre points per subinterval */
    const slong nsub = argc > 5 ? atol(argv[5]) : 45;   /* subintervals of width 1/10; multiple of 5 */
    if (nsub % 5) { fprintf(stderr, "nsub must be a multiple of 5\n"); return 1; }
    const double U = nsub / 10.0;   /* end of the Gauss-Legendre region (exact half-integer) */
    const double U2 = U + 4.5;      /* end of the outer region; Cramer tail beyond */

    /* constants */
    sq_a = _arb_vec_init(NMAX + 1); sq_b = _arb_vec_init(NMAX + 1); In_c = _arb_vec_init(NMAX + 1);
    for (slong n = 0; n <= NMAX; n++)
    {
        arb_set_ui(sq_a + n, 2); arb_div_ui(sq_a + n, sq_a + n, n + 1, prec); arb_sqrt(sq_a + n, sq_a + n, prec);
        arb_set_ui(sq_b + n, n); arb_div_ui(sq_b + n, sq_b + n, n + 1, prec); arb_sqrt(sq_b + n, sq_b + n, prec);
        if (n >= 1) { arb_const_pi(In_c + n, prec); arb_mul_ui(In_c + n, In_c + n, n, prec);
                      arb_ui_div(In_c + n, 2, In_c + n, prec); arb_sqrt(In_c + n, In_c + n, prec); }
    }
    arb_t pim14, pi, sqpi; arb_init(pim14); arb_init(pi); arb_init(sqpi);
    arb_const_pi(pi, prec); arb_sqrt(sqpi, pi, prec);
    arb_root_ui(pim14, pi, 4, prec); arb_inv(pim14, pim14, prec);
    if (strncmp(pf, "cq:", 3) == 0)
    {
        /* cubic-quintic scheme of Saha et al.: f(w,x) = sgn(w + theta He3(x)), theta = eta/sqrt(V),
           V = 1 + s3^2 + s5^2.  With w = sqrt2 z, x = sqrt2 u (variance 1/2) and He3(sqrt2 u) = psi_3(u):
           f = sign(z - a(u)), a(u) = -(theta/sqrt2) psi_3(u).  Acoef[j] multiplies psi_{2j+1}. */
        char tmp[256]; strncpy(tmp, pf + 3, 255); tmp[255] = 0;
        char *e1 = strtok(tmp, ":"), *e2 = strtok(NULL, ":"), *e3 = strtok(NULL, ":");
        if (!e1 || !e2 || !e3) { fprintf(stderr, "cq:eta:s3:s5 expected\n"); return 1; }
        arb_t eta, s3, s5, V, th; arb_init(eta); arb_init(s3); arb_init(s5); arb_init(V); arb_init(th);
        if (arb_set_str(eta, e1, prec) || arb_set_str(s3, e2, prec) || arb_set_str(s5, e3, prec)) { fprintf(stderr, "bad cq parameters\n"); return 1; }
        arb_sqr(s3, s3, prec); arb_sqr(s5, s5, prec); arb_add(V, s3, s5, prec); arb_add_ui(V, V, 1, prec);
        arb_rsqrt(th, V, prec); arb_mul(th, th, eta, prec);                 /* theta */
        for (int j = 0; j < NMODES; j++) { arb_init(Acoef[j]); arb_zero(Acoef[j]); }
        arb_sqrt_ui(V, 2, prec); arb_div(Acoef[1], th, V, prec); arb_neg(Acoef[1], Acoef[1]);
        fprintf(stderr, "cq profile: a(u) = "); arb_fprintn(stderr, Acoef[1], 20, 0); fprintf(stderr, " * psi_3(u)\n");
        arb_clear(eta); arb_clear(s3); arb_clear(s5); arb_clear(V); arb_clear(th);
    }
    else
    {
    FILE *fp = fopen(pf, "r"); char buf[128];
    for (int j = 0; j < NMODES; j++)
    {
        if (fscanf(fp, "%127s", buf) != 1) { fprintf(stderr, "profile read error\n"); return 1; }
        arb_init(Acoef[j]);
        if (arb_set_str(Acoef[j], buf, prec)) { fprintf(stderr, "bad number %s\n", buf); return 1; }
        arb_mul(Acoef[j], Acoef[j], pim14, prec);
    }
    fclose(fp);
    }

    /* subintervals of [0, U] = [0, 4.5]: centres (2s+1)/20 and half-width 1/20, s = 0..44, as Arb balls
       (exact rationals enclosed), so the subintervals tile [0, 4.5] exactly */

    /* Gauss-Legendre on [-1,1] */
    arb_ptr gx = _arb_vec_init(P), gw = _arb_vec_init(P);
    for (slong k = 0; k < P; k++) arb_hypgeom_legendre_p_ui_root(gx + k, gw + k, P, k, prec);

    slong M = N0 + 1, nn = nsub * P;
    arb_mat_t Psi, Imat, Alpha; arb_mat_init(Psi, M, nn); arb_mat_init(Imat, nn, M); arb_mat_init(Alpha, M, M);
    acb_ptr pv = _acb_vec_init(M), iv = _acb_vec_init(M);
    acb_t u, a, t; acb_init(u); acb_init(a); acb_init(t);
    arb_t c, h, w, ex; arb_init(c); arb_init(h); arb_init(w); arb_init(ex);

    slong col = 0;
    for (slong s = 0; s < nsub; s++)
    {
        arb_set_ui(c, 2 * s + 1); arb_div_ui(c, c, 20, prec); arb_one(h); arb_div_ui(h, h, 20, prec);
        for (slong k = 0; k < P; k++, col++)
        {
            arb_mul(w, gx + k, h, prec); arb_add(w, w, c, prec);     /* node */
            acb_set_arb(u, w);
            arb_sqr(ex, w, prec); arb_neg(ex, ex); arb_exp(ex, ex, prec);
            arb_mul(ex, ex, gw + k, prec); arb_mul(ex, ex, h, prec);
            arb_mul_ui(ex, ex, 2, prec); arb_div(ex, ex, sqpi, prec); /* 2 * w_k h e^{-u^2}/sqrt(pi) */
            psi_vec(pv, u, N0);
            profile(a, u);
            I_vec(iv, a, N0);
            for (slong m = 0; m < M; m++) arb_mul(arb_mat_entry(Psi, m, col), acb_realref(pv + m), ex, prec);
            for (slong n = 0; n < M; n++) arb_set(arb_mat_entry(Imat, col, n), acb_realref(iv + n));
        }
        if (s % 50 == 0) { fprintf(stderr, "nodes: subinterval %ld/%ld\n", s, nsub); }
    }
    fprintf(stderr, "matrix product...\n");
    arb_mat_mul(Alpha, Psi, Imat, prec);

    /* ---------- quadrature error bounds ---------- */
    const int NR = 4; double rhos[4] = {1.25, 1.6, 2.2, 3.5};
    const slong K = 128;  /* balls covering the ellipse boundary */
    mag_ptr Pm = _mag_vec_init(M), Qn = _mag_vec_init(M), Err = _mag_vec_init(M * M), best = _mag_vec_init(M * M);
    mag_t mg, cf, bnd; mag_init(mg); mag_init(cf); mag_init(bnd);
    acb_t e1, e2, z; acb_init(e1); acb_init(e2); acb_init(z);
    arb_t th, rad, rr, ri, coef; arb_init(th); arb_init(rad); arb_init(rr); arb_init(ri); arb_init(coef);
    for (slong s = 0; s < nsub; s++)
    {
        arb_set_ui(c, 2 * s + 1); arb_div_ui(c, c, 20, prec); arb_one(h); arb_div_ui(h, h, 20, prec);
        for (slong i = 0; i < M * M; i++) mag_inf(best + i);
        for (int r = 0; r < NR; r++)
        {
            arb_set_d(rr, rhos[r]); arb_inv(ri, rr, prec);
            for (slong m = 0; m < M; m++) { mag_zero(Pm + m); mag_zero(Qn + m); }
            for (slong j = 0; j < K; j++)
            {
                /* arc j: midpoint theta_j = 2 pi (j + 1/2)/K, half-width pi/K */
                arb_const_pi(th, prec); arb_mul_ui(th, th, 2 * j + 1, prec); arb_div_ui(th, th, K, prec);
                acb_set_arb(e1, th); acb_mul_onei(e1, e1); acb_exp(e1, e1, prec);
                acb_set_arb(e2, th); acb_mul_onei(e2, e2); acb_neg(e2, e2); acb_exp(e2, e2, prec);
                acb_mul_arb(e1, e1, rr, prec); acb_mul_arb(e2, e2, ri, prec);
                acb_add(z, e1, e2, prec); acb_mul_arb(z, z, h, prec); acb_mul_2exp_si(z, z, -1);
                acb_add_arb(u, z, c, prec);
                /* radius: (pi/K) * h (rho + 1/rho)/2 + rounding radius of u */
                {
                    mag_t rb, rx; mag_init(rb); mag_init(rx);
                    arb_add(rad, rr, ri, prec); arb_mul(rad, rad, h, prec); arb_mul_2exp_si(rad, rad, -1);
                    arb_const_pi(th, prec); arb_div_ui(th, th, K, prec); arb_mul(rad, rad, th, prec);
                    arb_get_mag(rb, rad);
                    mag_hypot(rx, arb_radref(acb_realref(u)), arb_radref(acb_imagref(u))); mag_add(rb, rb, rx);
                    acb_get_mid(u, u);
                    ball_bounds(Pm, Qn, u, rb, N0);
                    mag_clear(rb); mag_clear(rx);
                }
            }
            /* coef = h (64/15) rho^{-(2P-2)} / (rho^2 - 1) * 2 / sqrt(pi)   (Trefethen ATAP Thm 19.3 with n + 1 = P points) */
            arb_pow_ui(coef, rr, 2 * P - 2, prec); arb_inv(coef, coef, prec);
            arb_sqr(th, rr, prec); arb_sub_ui(th, th, 1, prec); arb_div(coef, coef, th, prec);
            arb_mul_ui(coef, coef, 128, prec); arb_div_ui(coef, coef, 15, prec);
            arb_mul(coef, coef, h, prec); arb_div(coef, coef, sqpi, prec);
            arb_get_mag(cf, coef);
            for (slong m = 0; m < M; m++)
                for (slong n = 0; n < M; n++)
                {
                    if (m + n > N0 || ((m + n) % 2) == 0) continue;
                    mag_mul(bnd, Pm + m, Qn + n); mag_mul(bnd, bnd, cf);
                    mag_min(best + m * M + n, best + m * M + n, bnd);
                }
        }
        for (slong i = 0; i < M * M; i++) mag_add(Err + i, Err + i, best + i);
        if (s % 20 == 0) fprintf(stderr, "error bounds: subinterval %ld/%ld\n", s, nsub);
    }
    /* ---------- outer region [U, U2]: classify cells by |a| >= 15 ---------- */
    {
        typedef struct { double lo, hi; int type, sg; } cell_t;
        slong cap = 1 << 22, ncell = 0, sp = 0;
        cell_t *cells = malloc(sizeof(cell_t) * cap), *stk = malloc(sizeof(cell_t) * 4096);
        for (slong i = 71; i >= 0; i--) { stk[sp].lo = U + i / 16.0; stk[sp].hi = U + (i + 1) / 16.0; sp++; }   /* exact doubles, 72 * 1/16 = 4.5 */
        acb_t c0, a0; acb_init(c0); acb_init(a0); mag_t r, ra, am; mag_init(r); mag_init(ra); mag_init(am);
        arb_t lb; arb_init(lb);
        while (sp > 0)
        {
            cell_t cl = stk[--sp];
            exact_cr(c0, r, cl.lo, cl.hi);
            profile_ball(a0, ra, c0, r);
            /* lower bound of |a| on the cell: |re a0| - rad - ra */
            arb_abs(lb, acb_realref(a0));
            arf_t lo15, rf; arf_init(lo15); arf_init(rf); arb_get_lbound_arf(lo15, lb, prec);
            arf_set_mag(rf, ra); arf_sub(lo15, lo15, rf, prec, ARF_RND_FLOOR);
            arf_set_mag(rf, arb_radref(acb_imagref(a0))); arf_sub(lo15, lo15, rf, prec, ARF_RND_FLOOR); arf_clear(rf);
            if (ncell >= cap - 1) { fprintf(stderr, "too many outer cells: enlarge nsub\n"); exit(1); }
            if (arf_cmp_si(lo15, 15) >= 0)
            { cl.type = 1; cl.sg = arf_sgn(arb_midref(acb_realref(a0))); cells[ncell++] = cl; }
            else if (cl.hi - cl.lo < 2e-8)
            { cl.type = 2; cl.sg = 0; cells[ncell++] = cl; }
            else
            {
                double mid = 0.5 * (cl.lo + cl.hi);
                cell_t c1 = { cl.lo, mid, 0, 0 }, c2 = { mid, cl.hi, 0, 0 };
                stk[sp++] = c2; stk[sp++] = c1;
            }
            arf_clear(lo15);
        }
        /* sort cells by lo (they are produced in order since the stack is processed left to right) */
        double rootw = 0; slong nroot = 0;
        for (slong i = 0; i < ncell; i++) if (cells[i].type == 2) { rootw += cells[i].hi - cells[i].lo; nroot++; }
        fprintf(stderr, "outer cells: %ld, root cells: %ld, total root width %.3e\n", ncell, nroot, rootw);

        mag_ptr S = _mag_vec_init(M), radn0 = _mag_vec_init(M), radn1 = _mag_vec_init(M);
        mag_t tmp, c2sp, e15, e112, wmag; mag_init(tmp); mag_init(c2sp); mag_init(e15); mag_init(e112); mag_init(wmag);
        arb_t tt; arb_init(tt);
        arb_set_ui(tt, 2); arb_div(tt, tt, sqpi, prec); arb_get_mag(c2sp, tt);             /* 2/sqrt(pi) */
        arb_set_ui(tt, 15); arb_hypgeom_erfc(tt, tt, prec); arb_get_mag(e15, tt);          /* erfc(15) */
        arb_set_si(tt, -112); arb_exp(tt, tt, prec); arb_get_mag(e112, tt);               /* e^{-112} */
        arb_ptr Jm = _arb_vec_init(M);
        /* merge sign cells into maximal intervals and integrate psi_m e^{-u^2} there */
        slong i = 0;
        while (i < ncell)
        {
            if (cells[i].type == 2)
            {
                psiexp_sup_interval(S, cells[i].lo, cells[i].hi, N0);
                mag_set_d(wmag, (cells[i].hi - cells[i].lo) * (1 + 1e-12));
                for (slong m = 0; m < M; m++) { mag_mul(tmp, S + m, wmag); mag_mul(tmp, tmp, c2sp); mag_add(radn0 + m, radn0 + m, tmp); mag_add(radn1 + m, radn1 + m, tmp); }
                i++; continue;
            }
            slong j = i; while (j + 1 < ncell && cells[j + 1].type == 1 && cells[j + 1].sg == cells[i].sg && cells[j + 1].lo == cells[j].hi) j++;
            double x0 = cells[i].lo, x1 = cells[j].hi; int sg = cells[i].sg;
            /* GL on pieces of width <= 0.05 */
            for (slong m = 0; m < M; m++) arb_zero(Jm + m);
            slong npc = (slong) ceil((x1 - x0) / 0.05); if (npc < 1) npc = 1;
            for (slong q = 0; q < npc; q++)
            {
                double pl = x0 + (x1 - x0) * q / npc, ph = (q + 1 == npc) ? x1 : x0 + (x1 - x0) * (q + 1) / npc;
                arb_t cc, hh; arb_init(cc); arb_init(hh);
                arb_set_d(cc, pl); arb_set_d(hh, ph); arb_add(cc, cc, hh, prec); arb_mul_2exp_si(cc, cc, -1);
                arb_set_d(hh, ph); arb_sub(hh, hh, cc, prec);
                for (slong k = 0; k < P; k++)
                {
                    arb_mul(w, gx + k, hh, prec); arb_add(w, w, cc, prec); acb_set_arb(u, w);
                    arb_sqr(ex, w, prec); arb_neg(ex, ex); arb_exp(ex, ex, prec); arb_mul(ex, ex, gw + k, prec); arb_mul(ex, ex, hh, prec);
                    psi_vec(pv, u, N0);
                    for (slong m = 0; m < M; m++) arb_addmul(Jm + m, acb_realref(pv + m), ex, prec);
                }
                /* quadrature error: ellipse rho = 3, sup |psi_m e^{-u^2}| on ellipse via a covering ball */
                {
                    acb_t ce; acb_init(ce); mag_t re, eb; mag_init(re); mag_init(eb);
                    double hd = ph - pl;  /* half-width = hd/2 */
                    arb_set(acb_realref(ce), cc); arb_zero(acb_imagref(ce)); acb_get_mid(ce, ce);
                    /* ellipse with rho = 3 lies in the disk of radius (hd/2) (3 + 1/3)/2 around the centre */
                    mag_set_d(re, 0.5 * hd * (3.0 + 1.0 / 3.0) / 2.0 * (1 + 1e-12) + 1e-300);
                    mag_ptr Se = _mag_vec_init(M);
                    psi_sup_ball(Se, ce, re, N0);
                    acb_t ub; acb_init(ub); acb_set(ub, ce); mag_add(arb_radref(acb_realref(ub)), arb_radref(acb_realref(ub)), re); mag_add(arb_radref(acb_imagref(ub)), arb_radref(acb_imagref(ub)), re);
                    acb_sqr(ub, ub, prec); acb_neg(ub, ub); acb_exp(ub, ub, prec); acb_get_mag(eb, ub);
                    /* coefficient: (hd/2) (64/15) 3^{-(2P-2)} / (9 - 1) */
                    arb_t cf; arb_init(cf); arb_set_ui(cf, 3); arb_pow_ui(cf, cf, 2 * P - 2, prec); arb_inv(cf, cf, prec);
                    arb_mul_ui(cf, cf, 64, prec); arb_div_ui(cf, cf, 15 * 8, prec); arb_mul(cf, cf, hh, prec);
                    mag_t cfm; mag_init(cfm); arb_get_mag(cfm, cf);
                    for (slong m = 0; m < M; m++) { mag_mul(tmp, Se + m, eb); mag_mul(tmp, tmp, cfm); arb_add_error_mag(Jm + m, tmp); }
                    _mag_vec_clear(Se, M); acb_clear(ub); acb_clear(ce); mag_clear(re); mag_clear(eb); mag_clear(cfm); arb_clear(cf);
                }
                /* erfc(15) and e^{-112} remainders on this piece */
                psiexp_sup_interval(S, pl, ph, N0);
                mag_set_d(wmag, (ph - pl) * (1 + 1e-12));
                for (slong m = 0; m < M; m++)
                {
                    mag_mul(tmp, S + m, wmag); mag_mul(tmp, tmp, c2sp);
                    mag_t t2; mag_init(t2);
                    mag_mul(t2, tmp, e15); mag_add(radn0 + m, radn0 + m, t2);
                    mag_mul(t2, tmp, e112); mag_add(radn1 + m, radn1 + m, t2);
                    mag_clear(t2);
                }
                arb_clear(cc); arb_clear(hh);
            }
            /* alpha_{m,0} += -sign * (2/sqrt(pi)) J_m */
            for (slong m = 0; m < M; m++)
            {
                if ((m % 2) == 0) continue;   /* m + 0 must be odd */
                arb_mul(tt, Jm + m, sqpi, prec); arb_inv(ex, sqpi, prec); arb_mul_ui(ex, ex, 2, prec); arb_mul(tt, Jm + m, ex, prec);
                if (sg > 0) arb_sub(arb_mat_entry(Alpha, m, 0), arb_mat_entry(Alpha, m, 0), tt, prec);
                else arb_add(arb_mat_entry(Alpha, m, 0), arb_mat_entry(Alpha, m, 0), tt, prec);
            }
            i = j + 1;
        }
        for (slong m = 0; m < M; m++)
            for (slong n = 0; n < M; n++)
            {
                if (m + n > N0 || ((m + n) % 2) == 0) continue;
                arb_add_error_mag(arb_mat_entry(Alpha, m, n), n == 0 ? radn0 + m : radn1 + m);
            }
        fprintf(stderr, "outer radii: n=0 max "); { double mx = 0; for (slong m = 0; m < M; m++) if (mag_get_d(radn0 + m) > mx) mx = mag_get_d(radn0 + m); fprintf(stderr, "%.3e, n>=1 max ", mx); mx = 0; for (slong m = 0; m < M; m++) if (mag_get_d(radn1 + m) > mx) mx = mag_get_d(radn1 + m); fprintf(stderr, "%.3e\n", mx); }
        free(cells); free(stk);
    }

    /* tail u > U2 (continued): (2/sqrt(pi)) 1.0865 sqrt(pi/2) erfc(U/sqrt 2) = 1.0865 sqrt(2) erfc(U/sqrt2) */
    arb_t tl; arb_init(tl);
    arb_set_d(tl, U2); arb_sqrt_ui(th, 2, prec); arb_div(tl, tl, th, prec); arb_hypgeom_erfc(tl, tl, prec);
    arb_mul(tl, tl, th, prec); arb_set_str(rr, "1.0865", prec); arb_mul(tl, tl, rr, prec);
    mag_t tm; mag_init(tm); arb_get_mag(tm, tl);

    FILE *out = fopen(of, "w");
    for (slong m = 0; m < M; m++)
        for (slong n = 0; n < M; n++)
        {
            if (m + n > N0 || ((m + n) % 2) == 0) continue;
            arb_ptr x = arb_mat_entry(Alpha, m, n);
            arb_add_error_mag(x, Err + m * M + n);
            arb_add_error_mag(x, tm);
            char *str = arb_dump_str(x);
            fprintf(out, "%ld %ld %s\n", m, n, str);
            flint_free(str);
        }
    fclose(out);
    fprintf(stderr, "done; tail bound = "); mag_fprint(stderr, tm); fprintf(stderr, "\n");
    return 0;
}
