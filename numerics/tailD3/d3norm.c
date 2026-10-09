/*
  d3norm.c -- rigorous upper bound for the boundary energy of the third Euler derivative of the
  correlation function of a "polynomial threshold" limiting Krivine scheme

      f(w,x) = sgn(w + P(x)),  g(w,x) = f(w,-x),  corr(W,W') = rho(t),  corr(X,X') = t,
      H(t) = (pi/2) E[f g] = T_{-t}[ Psi_t ],   Psi_t(x,y) = K_{rho(t)}(P(x), P(y)),
      K_r(u,v) = (pi/2) E[sgn(Z1-u) sgn(Z2-v)],  corr(Z1,Z2) = r,
      T_s G = sum_n s^n G^_{nn}  (Mehler trace),  D = t d/dt.

  Derivation (checked independently in this file's test mode against the Taylor coefficients):
    D T_{-t}[Psi] = T_{-t}[D Psi - t d_x d_y Psi]; iterating three times,
      D^3 H(t) = T_{-t}[Phi_3],  Phi_3 = sum_{(p,a)} kappa_{pa}(t) d_r^p (d_x d_y)^a K_r(P(x),P(y)) |_{r=rho(t)},
    kappa: (1,0) q3, (2,0) 3 q1 q2, (3,0) q1^3, (0,1) -t, (0,2) 3t^2, (0,3) -t^3,
           (1,1) -3t(q1+q2), (2,1) -3t q1^2, (1,2) 3t^2 q1,      q_j = D^j rho.
    d_r K = d_u d_v K = 2 pi phi_r,  d_r phi = d_u d_v phi  (phi_r the bivariate standard normal density),
    d_x^a g(P(x)) = sum_i B_{a,i}(x) g^(i)(P(x)),  B_{a+1,i} = B_{a,i}' + P' B_{a,i-1},
    2 pi d_u^i d_v^j phi_r = d^{-1/2} F_{ij} exp(-(u^2 - 2ruv + v^2)/(2d)),  d = 1 - r^2,
      F_00 = 1, F_0j = l_v F_0,j-1 - (j-1)/d F_0,j-2,
      F_ij = l_u F_i-1,j - (i-1)/d F_i-2,j + j r/d F_i-1,j-1,  l_u = (rv-u)/d, l_v = (ru-v)/d.
  Hence (d_x d_y)^e Phi_3 = d^{-1/2} R_e exp(-(u^2-2ruv+v^2)/(2d)) with
      R_e = sum_{(p,a)} kappa_pa sum_{i,j} B_{a+e,i}(x) B_{a+e,j}(y) F_{i+p-1, j+p-1}   (p >= 1),
      R_e = sum ... F_{i-1, j-1}, i, j >= 1                                              (p = 0),
  and for a real-coefficient scheme with |rho| <= 1 on the closed disk the weighted trace bound
      |T_s G|^2 <= C_a ( ||G||^2 + a ||d_x d_y G||^2 ),  C_a = sum_{n>=0} 1/(1+a n^2) = 1/2 + pi/(2 sqrt a) coth(pi/sqrt a)
  gives  sum_m m^6 b_m^2 = ||D^3 H||^2_{L2(T)} <= C_a (J_0 + a J_1),
      J_e = (1/pi) int_0^pi || (d_x d_y)^e Phi_3(e^{i theta}) ||^2_{L2(gamma x gamma)} dtheta
          = (1/pi) int_0^pi int int |R_e|^2 / (2 pi |d|) exp(-Re(Q/d) - (x^2+y^2)/2) dx dy dtheta.
  Re(Q/d) = (A-B)(u+v)^2/2 + (A+B)(u-v)^2/2 with A-B = Re 1/(1+r) >= 1/2, A+B = Re 1/(1-r) >= 1/2 (|r| <= 1).

  This program bounds J_0 and J_1 from above by an adaptive box partition of [0, X0] x [-X0, X0] x [0, pi]
  (the integrand is invariant under (x,y) -> (-x,-y)) in Arb ball arithmetic, plus an analytic bound
  for the exterior max(|x|,|y|) > X0.

  usage: d3norm SCHEME X0 eta tau maxboxes        SCHEME = cq:eta:s3:s5  or  he:Pfile:rhofile
         d3norm SCHEME test t                       (consistency test of the kernel formula at real t)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/arb_poly.h>
#include <flint/acb_poly.h>
#include <flint/arb_hypgeom.h>

static slong prec = 64;
static arb_poly_t Pm;          /* threshold P(x), monomial basis */
static arb_poly_t Bell[5][5];  /* B_{a,i}(x), a <= 4 */
static acb_poly_t rho;         /* rho(t) */
static acb_poly_t Drho[4];     /* D^j rho, j = 0..3 */

/* ---------- scheme setup ---------- */
static void hermite_orthonormal_to_monomial(arb_poly_t out, const arb_ptr c, slong deg)
{
    /* h_0 = 1, h_1 = x, h_{j+1} = (x h_j - sqrt(j) h_{j-1}) / sqrt(j+1) */
    arb_poly_t h0, h1, h2, tmp; arb_poly_init(h0); arb_poly_init(h1); arb_poly_init(h2); arb_poly_init(tmp);
    arb_t s; arb_init(s);
    arb_poly_one(h0); arb_poly_zero(h1); arb_poly_set_coeff_si(h1, 1, 1);
    arb_poly_zero(out);
    arb_poly_scalar_mul(tmp, h0, c + 0, prec); arb_poly_add(out, out, tmp, prec);
    if (deg >= 1) { arb_poly_scalar_mul(tmp, h1, c + 1, prec); arb_poly_add(out, out, tmp, prec); }
    for (slong j = 1; j < deg; j++)
    {
        arb_poly_shift_left(h2, h1, 1);
        arb_sqrt_ui(s, j, prec); arb_poly_scalar_mul(tmp, h0, s, prec); arb_poly_sub(h2, h2, tmp, prec);
        arb_sqrt_ui(s, j + 1, prec); arb_poly_scalar_div(h2, h2, s, prec);
        arb_poly_scalar_mul(tmp, h2, c + j + 1, prec); arb_poly_add(out, out, tmp, prec);
        arb_poly_swap(h0, h1); arb_poly_swap(h1, h2);
    }
    arb_poly_clear(h0); arb_poly_clear(h1); arb_poly_clear(h2); arb_poly_clear(tmp); arb_clear(s);
}

static void setup_scheme(const char *sch)
{
    arb_poly_init(Pm); acb_poly_init(rho);
    if (strncmp(sch, "cq:", 3) == 0)
    {
        char tmp[256]; strncpy(tmp, sch + 3, 255); tmp[255] = 0;
        char *e1 = strtok(tmp, ":"), *e2 = strtok(NULL, ":"), *e3 = strtok(NULL, ":");
        arb_t eta, s3, s5, V, th, x; arb_init(eta); arb_init(s3); arb_init(s5); arb_init(V); arb_init(th); arb_init(x);
        arb_set_str(eta, e1, 4 * prec); arb_set_str(s3, e2, 4 * prec); arb_set_str(s5, e3, 4 * prec);
        arb_sqr(s3, s3, 4 * prec); arb_sqr(s5, s5, 4 * prec); arb_add(V, s3, s5, 4 * prec); arb_add_ui(V, V, 1, 4 * prec);
        arb_rsqrt(th, V, 4 * prec); arb_mul(th, th, eta, 4 * prec);
        /* P(x) = theta He3(x) = theta (x^3 - 3x)/sqrt 6 */
        arb_rsqrt_ui(x, 6, 4 * prec); arb_mul(x, x, th, 4 * prec);
        arb_poly_set_coeff_arb(Pm, 3, x); arb_mul_si(x, x, -3, 4 * prec); arb_poly_set_coeff_arb(Pm, 1, x);
        acb_t z; acb_init(z);
        arb_inv(x, V, 4 * prec); acb_set_arb(z, x); acb_poly_set_coeff_acb(rho, 1, z);
        arb_div(x, s3, V, 4 * prec); arb_neg(x, x); acb_set_arb(z, x); acb_poly_set_coeff_acb(rho, 3, z);
        arb_div(x, s5, V, 4 * prec); acb_set_arb(z, x); acb_poly_set_coeff_acb(rho, 5, z);
        acb_clear(z);
    }
    else if (strncmp(sch, "he:", 3) == 0)
    {
        char tmp[512]; strncpy(tmp, sch + 3, 511); tmp[511] = 0;
        char *fp = strtok(tmp, ":"), *fr = strtok(NULL, ":");
        arb_ptr c = _arb_vec_init(102); long j; char buf[128];
        FILE *f = fopen(fp, "r"); while (fscanf(f, "%ld %127s", &j, buf) == 2) arb_set_str(c + j, buf, 4 * prec); fclose(f);
        slong deg = 0; for (slong k = 0; k < 102; k++) if (!arb_is_zero(c + k)) deg = k;
        hermite_orthonormal_to_monomial(Pm, c, deg);
        f = fopen(fr, "r"); acb_t z; acb_init(z);
        while (fscanf(f, "%ld %127s", &j, buf) == 2) { arb_set_str(acb_realref(z), buf, 4 * prec); arb_zero(acb_imagref(z)); acb_poly_set_coeff_acb(rho, j, z); }
        fclose(f); acb_clear(z);
    }
    else { fprintf(stderr, "unknown scheme\n"); exit(2); }
    /* Bell polynomials */
    arb_poly_t dP, tmp; arb_poly_init(dP); arb_poly_init(tmp); arb_poly_derivative(dP, Pm, prec);
    for (int a = 0; a < 5; a++) for (int i = 0; i < 5; i++) arb_poly_init(Bell[a][i]);
    arb_poly_one(Bell[0][0]);
    for (int a = 0; a < 4; a++)
        for (int i = 0; i <= a + 1; i++)
        {
            arb_poly_zero(Bell[a + 1][i]);
            if (i <= a) arb_poly_derivative(Bell[a + 1][i], Bell[a][i], prec);
            if (i >= 1) { arb_poly_mul(tmp, dP, Bell[a][i - 1], prec); arb_poly_add(Bell[a + 1][i], Bell[a + 1][i], tmp, prec); }
        }
    /* D^j rho: multiply coefficient k by k^j */
    for (int jj = 0; jj < 4; jj++)
    {
        acb_poly_init(Drho[jj]); acb_poly_set(Drho[jj], rho);
        for (slong k = 0; k < acb_poly_length(rho); k++)
        { acb_t z; acb_init(z); acb_poly_get_coeff_acb(z, rho, k); for (int q = 0; q < jj; q++) acb_mul_si(z, z, k, prec); acb_poly_set_coeff_acb(Drho[jj], k, z); acb_clear(z); }
    }
    arb_poly_clear(dP); arb_poly_clear(tmp);
}

/* ---------- integrand ---------- */
/* For x, y real balls and t a complex ball: R2[e] = |R_e|^2 (balls), and the quantities for the exponent. */
typedef struct { arb_t R2[2], dabs, AmB, ApB, u, v; acb_t R0, dd; } evalres;

static void evalres_init(evalres *E) { acb_init(E->R0); acb_init(E->dd); for (int e = 0; e < 2; e++) arb_init(E->R2[e]); arb_init(E->dabs); arb_init(E->AmB); arb_init(E->ApB); arb_init(E->u); arb_init(E->v); }

static void eval_point(evalres *E, const arb_t x, const arb_t y, const acb_t t)
{
    arb_t Bx[5][5], By[5][5]; acb_t q[4], r, d, dinv, lu, lv, F[4][4], tmp, tmp2, kap, Re[2];
    for (int a = 0; a < 5; a++) for (int i = 0; i < 5; i++) { arb_init(Bx[a][i]); arb_init(By[a][i]); }
    for (int j = 0; j < 4; j++) acb_init(q[j]);
    acb_init(r); acb_init(d); acb_init(dinv); acb_init(lu); acb_init(lv); acb_init(tmp); acb_init(tmp2); acb_init(kap); acb_init(Re[0]); acb_init(Re[1]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) acb_init(F[i][j]);

    arb_poly_evaluate(E->u, Pm, x, prec); arb_poly_evaluate(E->v, Pm, y, prec);
    for (int a = 0; a < 5; a++) for (int i = 0; i <= a; i++) { arb_poly_evaluate(Bx[a][i], Bell[a][i], x, prec); arb_poly_evaluate(By[a][i], Bell[a][i], y, prec); }
    for (int j = 0; j < 4; j++) acb_poly_evaluate(q[j], Drho[j], t, prec);
    acb_set(r, q[0]);
    acb_sqr(d, r, prec); acb_neg(d, d); acb_add_ui(d, d, 1, prec);       /* d = 1 - r^2 */
    acb_inv(dinv, d, prec);
    acb_abs(E->dabs, d, prec);
    /* A - B = Re 1/(1+r), A + B = Re 1/(1-r) */
    acb_add_ui(tmp, r, 1, prec); acb_inv(tmp, tmp, prec); arb_set(E->AmB, acb_realref(tmp));
    acb_neg(tmp, r); acb_add_ui(tmp, tmp, 1, prec); acb_inv(tmp, tmp, prec); arb_set(E->ApB, acb_realref(tmp));
    /* l_u = (r v - u)/d, l_v = (r u - v)/d */
    acb_mul_arb(lu, r, E->v, prec); acb_sub_arb(lu, lu, E->u, prec); acb_mul(lu, lu, dinv, prec);
    acb_mul_arb(lv, r, E->u, prec); acb_sub_arb(lv, lv, E->v, prec); acb_mul(lv, lv, dinv, prec);
    acb_one(F[0][0]);
    for (int j = 1; j < 4; j++)
    {
        acb_mul(F[0][j], lv, F[0][j - 1], prec);
        if (j >= 2) { acb_mul_si(tmp, dinv, j - 1, prec); acb_mul(tmp, tmp, F[0][j - 2], prec); acb_sub(F[0][j], F[0][j], tmp, prec); }
    }
    for (int i = 1; i < 4; i++)
        for (int j = 0; j < 4; j++)
        {
            acb_mul(F[i][j], lu, F[i - 1][j], prec);
            if (i >= 2) { acb_mul_si(tmp, dinv, i - 1, prec); acb_mul(tmp, tmp, F[i - 2][j], prec); acb_sub(F[i][j], F[i][j], tmp, prec); }
            if (j >= 1) { acb_mul(tmp, r, dinv, prec); acb_mul_si(tmp, tmp, j, prec); acb_mul(tmp, tmp, F[i - 1][j - 1], prec); acb_add(F[i][j], F[i][j], tmp, prec); }
        }
    /* kappa table */
    static const int PA[9][2] = { {1,0},{2,0},{3,0},{0,1},{0,2},{0,3},{1,1},{2,1},{1,2} };
    for (int e = 0; e < 2; e++) acb_zero(Re[e]);
    for (int k = 0; k < 9; k++)
    {
        int p = PA[k][0], a = PA[k][1];
        switch (k)
        {
            case 0: acb_set(kap, q[3]); break;
            case 1: acb_mul(kap, q[1], q[2], prec); acb_mul_si(kap, kap, 3, prec); break;
            case 2: acb_pow_ui(kap, q[1], 3, prec); break;
            case 3: acb_neg(kap, t); break;
            case 4: acb_sqr(kap, t, prec); acb_mul_si(kap, kap, 3, prec); break;
            case 5: acb_pow_ui(kap, t, 3, prec); acb_neg(kap, kap); break;
            case 6: acb_add(kap, q[1], q[2], prec); acb_mul(kap, kap, t, prec); acb_mul_si(kap, kap, -3, prec); break;
            case 7: acb_sqr(kap, q[1], prec); acb_mul(kap, kap, t, prec); acb_mul_si(kap, kap, -3, prec); break;
            case 8: acb_sqr(kap, t, prec); acb_mul(kap, kap, q[1], prec); acb_mul_si(kap, kap, 3, prec); break;
        }
        for (int e = 0; e < 2; e++)
        {
            int aa = a + e; acb_zero(tmp2);
            for (int i = 0; i <= aa; i++) for (int j = 0; j <= aa; j++)
            {
                int fi, fj;
                if (p >= 1) { fi = i + p - 1; fj = j + p - 1; }
                else { if (i == 0 || j == 0) continue; fi = i - 1; fj = j - 1; }
                if (arb_is_zero(Bx[aa][i]) || arb_is_zero(By[aa][j])) continue;
                acb_mul_arb(tmp, F[fi][fj], Bx[aa][i], prec); acb_mul_arb(tmp, tmp, By[aa][j], prec); acb_add(tmp2, tmp2, tmp, prec);
            }
            acb_mul(tmp, tmp2, kap, prec); acb_add(Re[e], Re[e], tmp, prec);
        }
    }
    acb_set(E->R0, Re[0]); acb_set(E->dd, d);
    for (int e = 0; e < 2; e++) { acb_abs(E->R2[e], Re[e], prec); arb_sqr(E->R2[e], E->R2[e], prec); }

    for (int a = 0; a < 5; a++) for (int i = 0; i < 5; i++) { arb_clear(Bx[a][i]); arb_clear(By[a][i]); }
    for (int j = 0; j < 4; j++) acb_clear(q[j]);
    acb_clear(r); acb_clear(d); acb_clear(dinv); acb_clear(lu); acb_clear(lv); acb_clear(tmp); acb_clear(tmp2); acb_clear(kap); acb_clear(Re[0]); acb_clear(Re[1]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) acb_clear(F[i][j]);
}

/* upper bounds (doubles, rounded up) of the two integrands on a box; also center values */
static double half_lb = 0.5;
static arb_struct *g_R2mv = NULL;   /* optional second enclosure of |R_e|^2 (mean-value form) */
static void box_ub(double out[2], const arb_t x, const arb_t y, const acb_t t)
{
    evalres E; evalres_init(&E);
    eval_point(&E, x, y, t);
    arb_t s, q, ex, pre; arb_init(s); arb_init(q); arb_init(ex); arb_init(pre);
    arf_t lb; arf_init(lb);
    /* exponent lower bound: 0.5 (A-B)(u+v)^2 + 0.5 (A+B)(u-v)^2 + 0.5 (x^2 + y^2), each factor lower-bounded */
    double cAmB, cApB;
    arb_get_lbound_arf(lb, E.AmB, prec); cAmB = arf_get_d(lb, ARF_RND_DOWN); if (!(cAmB > half_lb)) cAmB = half_lb;
    arb_get_lbound_arf(lb, E.ApB, prec); cApB = arf_get_d(lb, ARF_RND_DOWN); if (!(cApB > half_lb)) cApB = half_lb;
    arb_add(s, E.u, E.v, prec); arb_sqr(s, s, prec); arb_get_lbound_arf(lb, s, prec); double sp = arf_get_d(lb, ARF_RND_DOWN); if (sp < 0) sp = 0;
    arb_sub(s, E.u, E.v, prec); arb_sqr(s, s, prec); arb_get_lbound_arf(lb, s, prec); double sm = arf_get_d(lb, ARF_RND_DOWN); if (sm < 0) sm = 0;
    arb_sqr(s, x, prec); arb_sqr(q, y, prec); arb_add(s, s, q, prec); arb_get_lbound_arf(lb, s, prec); double sx = arf_get_d(lb, ARF_RND_DOWN); if (sx < 0) sx = 0;
    double expo = 0.5 * cAmB * sp + 0.5 * cApB * sm + 0.5 * sx;
    expo *= (1 - 1e-12);
    /* prefactor 1/(2 pi |d|) upper bound */
    arb_get_lbound_arf(lb, E.dabs, prec); double dl = arf_get_d(lb, ARF_RND_DOWN);
    double prefac = (dl > 0) ? 1.0 / (2 * M_PI * dl) * (1 + 1e-12) : INFINITY;
    double ee = exp(-expo) * (1 + 1e-12);
    for (int e = 0; e < 2; e++)
    {
        arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, E.R2[e], prec); double R = arf_get_d(ub, ARF_RND_UP); arf_clear(ub);
        if (!arb_is_finite(E.R2[e])) R = INFINITY;
        if (g_R2mv != NULL && arb_is_finite(g_R2mv + e))
        { arf_t u2; arf_init(u2); arb_get_ubound_arf(u2, g_R2mv + e, prec); double R2 = arf_get_d(u2, ARF_RND_UP); arf_clear(u2); if (R2 < R) R = R2; }
        out[e] = R * prefac * ee * (1 + 1e-12);
    }
    arb_clear(s); arb_clear(q); arb_clear(ex); arb_clear(pre); arf_clear(lb);
    for (int e = 0; e < 2; e++) { arb_clear(E.R2[e]); } arb_clear(E.dabs); arb_clear(E.AmB); arb_clear(E.ApB); arb_clear(E.u); arb_clear(E.v);
}

static void set_interval(arb_t z, double lo, double hi)
{
    arb_set_d(z, lo); arb_t h; arb_init(h); arb_set_d(h, hi); arb_union(z, z, h, prec); arb_clear(h);
}


/* ---------- first-order jets (value, derivative in one variable) for mean-value enclosures of R_e ---------- */
typedef struct { acb_t v, d; } jet;
static void jinit(jet *a) { acb_init(a->v); acb_init(a->d); }
static void jclear(jet *a) { acb_clear(a->v); acb_clear(a->d); }
static void jset(jet *a, const jet *b) { acb_set(a->v, b->v); acb_set(a->d, b->d); }
static void jconst_si(jet *a, slong c) { acb_set_si(a->v, c); acb_zero(a->d); }
static void jadd(jet *r, const jet *a, const jet *b) { acb_add(r->v, a->v, b->v, prec); acb_add(r->d, a->d, b->d, prec); }
static void jsub(jet *r, const jet *a, const jet *b) { acb_sub(r->v, a->v, b->v, prec); acb_sub(r->d, a->d, b->d, prec); }
static void jmul(jet *r, const jet *a, const jet *b)
{ acb_t t1, t2; acb_init(t1); acb_init(t2); acb_mul(t1, a->d, b->v, prec); acb_mul(t2, a->v, b->d, prec); acb_add(t1, t1, t2, prec); acb_mul(r->v, a->v, b->v, prec); acb_swap(r->d, t1); acb_clear(t1); acb_clear(t2); }
static void jmul_si(jet *r, const jet *a, slong c) { acb_mul_si(r->v, a->v, c, prec); acb_mul_si(r->d, a->d, c, prec); }
static void jinv(jet *r, const jet *a)
{ acb_t iv; acb_init(iv); acb_inv(iv, a->v, prec); acb_mul(r->d, a->d, iv, prec); acb_mul(r->d, r->d, iv, prec); acb_neg(r->d, r->d); acb_swap(r->v, iv); acb_clear(iv); }
static void jpoly_arb(jet *r, const arb_poly_t p, const jet *x)
{ jet acc, c; jinit(&acc); jinit(&c); acb_zero(acc.v); acb_zero(acc.d);
  for (slong k = arb_poly_length(p) - 1; k >= 0; k--) { jmul(&acc, &acc, x); acb_set_arb(c.v, arb_poly_get_coeff_ptr(p, k)); acb_zero(c.d); jadd(&acc, &acc, &c); }
  jset(r, &acc); jclear(&acc); jclear(&c); }
static void jpoly_acb(jet *r, const acb_poly_t p, const jet *x)
{ jet acc, c; jinit(&acc); jinit(&c); acb_zero(acc.v); acb_zero(acc.d);
  for (slong k = acb_poly_length(p) - 1; k >= 0; k--) { jmul(&acc, &acc, x); acb_poly_get_coeff_acb(c.v, p, k); acb_zero(c.d); jadd(&acc, &acc, &c); }
  jset(r, &acc); jclear(&acc); jclear(&c); }

/* R_0, R_1 as jets */
static void eval_R_jet(jet R[2], const jet *x, const jet *y, const jet *t)
{
    jet u, v, Bx[5][5], By[5][5], q[4], r, d, di, lu, lv, F[4][4], tmp, tmp2, kap, one;
    jinit(&u); jinit(&v); jinit(&r); jinit(&d); jinit(&di); jinit(&lu); jinit(&lv); jinit(&tmp); jinit(&tmp2); jinit(&kap); jinit(&one);
    for (int a = 0; a < 5; a++) for (int i = 0; i < 5; i++) { jinit(&Bx[a][i]); jinit(&By[a][i]); }
    for (int j = 0; j < 4; j++) jinit(&q[j]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) jinit(&F[i][j]);
    jconst_si(&one, 1);
    jpoly_arb(&u, Pm, x); jpoly_arb(&v, Pm, y);
    for (int a = 0; a < 5; a++) for (int i = 0; i <= a; i++) { jpoly_arb(&Bx[a][i], Bell[a][i], x); jpoly_arb(&By[a][i], Bell[a][i], y); }
    for (int j = 0; j < 4; j++) jpoly_acb(&q[j], Drho[j], t);
    jset(&r, &q[0]);
    jmul(&d, &r, &r); jsub(&d, &one, &d); jinv(&di, &d);
    jmul(&lu, &r, &v); jsub(&lu, &lu, &u); jmul(&lu, &lu, &di);
    jmul(&lv, &r, &u); jsub(&lv, &lv, &v); jmul(&lv, &lv, &di);
    jconst_si(&F[0][0], 1);
    for (int j = 1; j < 4; j++) { jmul(&F[0][j], &lv, &F[0][j - 1]); if (j >= 2) { jmul_si(&tmp, &di, j - 1); jmul(&tmp, &tmp, &F[0][j - 2]); jsub(&F[0][j], &F[0][j], &tmp); } }
    for (int i = 1; i < 4; i++) for (int j = 0; j < 4; j++)
    {
        jmul(&F[i][j], &lu, &F[i - 1][j]);
        if (i >= 2) { jmul_si(&tmp, &di, i - 1); jmul(&tmp, &tmp, &F[i - 2][j]); jsub(&F[i][j], &F[i][j], &tmp); }
        if (j >= 1) { jmul(&tmp, &r, &di); jmul_si(&tmp, &tmp, j); jmul(&tmp, &tmp, &F[i - 1][j - 1]); jadd(&F[i][j], &F[i][j], &tmp); }
    }
    static const int PA[9][2] = { {1,0},{2,0},{3,0},{0,1},{0,2},{0,3},{1,1},{2,1},{1,2} };
    for (int e = 0; e < 2; e++) { acb_zero(R[e].v); acb_zero(R[e].d); }
    for (int k = 0; k < 9; k++)
    {
        int p = PA[k][0], a = PA[k][1];
        switch (k)
        {
            case 0: jset(&kap, &q[3]); break;
            case 1: jmul(&kap, &q[1], &q[2]); jmul_si(&kap, &kap, 3); break;
            case 2: jmul(&kap, &q[1], &q[1]); jmul(&kap, &kap, &q[1]); break;
            case 3: jmul_si(&kap, t, -1); break;
            case 4: jmul(&kap, t, t); jmul_si(&kap, &kap, 3); break;
            case 5: jmul(&kap, t, t); jmul(&kap, &kap, t); jmul_si(&kap, &kap, -1); break;
            case 6: jadd(&kap, &q[1], &q[2]); jmul(&kap, &kap, t); jmul_si(&kap, &kap, -3); break;
            case 7: jmul(&kap, &q[1], &q[1]); jmul(&kap, &kap, t); jmul_si(&kap, &kap, -3); break;
            case 8: jmul(&kap, t, t); jmul(&kap, &kap, &q[1]); jmul_si(&kap, &kap, 3); break;
        }
        for (int e = 0; e < 2; e++)
        {
            int aa = a + e; acb_zero(tmp2.v); acb_zero(tmp2.d);
            for (int i = 0; i <= aa; i++) for (int j = 0; j <= aa; j++)
            {
                int fi, fj;
                if (p >= 1) { fi = i + p - 1; fj = j + p - 1; } else { if (i == 0 || j == 0) continue; fi = i - 1; fj = j - 1; }
                if (arb_poly_is_zero(Bell[aa][i]) || arb_poly_is_zero(Bell[aa][j])) continue;
                jmul(&tmp, &F[fi][fj], &Bx[aa][i]); jmul(&tmp, &tmp, &By[aa][j]); jadd(&tmp2, &tmp2, &tmp);
            }
            jmul(&tmp, &tmp2, &kap); jadd(&R[e], &R[e], &tmp);
        }
    }
    jclear(&u); jclear(&v); jclear(&r); jclear(&d); jclear(&di); jclear(&lu); jclear(&lv); jclear(&tmp); jclear(&tmp2); jclear(&kap); jclear(&one);
    for (int a = 0; a < 5; a++) for (int i = 0; i < 5; i++) { jclear(&Bx[a][i]); jclear(&By[a][i]); }
    for (int j = 0; j < 4; j++) jclear(&q[j]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) jclear(&F[i][j]);
}

/* mean-value enclosure of |R_e|^2 on the box (x, y real intervals; theta interval) */
static void R2_meanvalue(arb_t out[2], double x0, double x1, double y0, double y1, double t0, double t1)
{
    double xc = 0.5 * (x0 + x1), yc = 0.5 * (y0 + y1), tc = 0.5 * (t0 + t1);
    double h[3] = { 0.5 * (x1 - x0) * (1 + 1e-12), 0.5 * (y1 - y0) * (1 + 1e-12), 0.5 * (t1 - t0) * (1 + 1e-12) };
    jet X, Y, T, R[2]; jinit(&X); jinit(&Y); jinit(&T); jinit(&R[0]); jinit(&R[1]);
    acb_t Rc[2]; acb_init(Rc[0]); acb_init(Rc[1]);
    arb_t th; arb_init(th);
    /* center */
    acb_set_d(X.v, xc); acb_zero(X.d); acb_set_d(Y.v, yc); acb_zero(Y.d);
    arb_set_d(th, tc); arb_sin_cos(acb_imagref(T.v), acb_realref(T.v), th, prec); acb_zero(T.d);
    eval_R_jet(R, &X, &Y, &T); acb_set(Rc[0], R[0].v); acb_set(Rc[1], R[1].v);
    for (int k = 0; k < 3; k++)
    {
        set_interval(acb_realref(X.v), x0, x1); arb_zero(acb_imagref(X.v)); acb_set_si(X.d, k == 0);
        set_interval(acb_realref(Y.v), y0, y1); arb_zero(acb_imagref(Y.v)); acb_set_si(Y.d, k == 1);
        set_interval(th, t0, t1); arb_sin_cos(acb_imagref(T.v), acb_realref(T.v), th, prec);
        if (k == 2) acb_mul_onei(T.d, T.v); else acb_zero(T.d);      /* d/dtheta e^{i theta} = i e^{i theta} */
        eval_R_jet(R, &X, &Y, &T);
        for (int e = 0; e < 2; e++) { mag_t m, hm; mag_init(m); mag_init(hm); acb_get_mag(m, R[e].d); mag_set_d(hm, h[k]); mag_mul(m, m, hm); acb_add_error_mag(Rc[e], m); mag_clear(m); mag_clear(hm); }
    }
    for (int e = 0; e < 2; e++) { acb_abs(out[e], Rc[e], prec); arb_sqr(out[e], out[e], prec); }
    jclear(&X); jclear(&Y); jclear(&T); jclear(&R[0]); jclear(&R[1]); acb_clear(Rc[0]); acb_clear(Rc[1]); arb_clear(th);
}

static int use_mv = 1;
static void R2_meanvalue(arb_t out[2], double x0, double x1, double y0, double y1, double t0, double t1);
static void eval_box(double out[2], double x0, double x1, double y0, double y1, double t0, double t1)
{
    arb_t x, y, th; acb_t t; arb_init(x); arb_init(y); arb_init(th); acb_init(t);
    set_interval(x, x0, x1); set_interval(y, y0, y1); set_interval(th, t0, t1);
    arb_sin_cos(acb_imagref(t), acb_realref(t), th, prec);
    arb_ptr mv = NULL;
    if (use_mv && (x1 > x0 || y1 > y0 || t1 > t0)) { mv = _arb_vec_init(2); R2_meanvalue((arb_t *) mv, x0, x1, y0, y1, t0, t1); }
    g_R2mv = mv;
    box_ub(out, x, y, t);
    g_R2mv = NULL;
    if (mv) _arb_vec_clear(mv, 2);
    arb_clear(x); arb_clear(y); arb_clear(th); acb_clear(t);
}

/* ---------- test mode: T_{-t}[Phi_3] at real t, i.e. E[Phi_3(X,Y)] with corr(X,Y) = -t, by a double-precision
   tensor trapezoid rule; to be compared with D^3 H(t) = sum m^3 b_m t^m from the coefficient head ---------- */
static void test_mode(double tval)
{
    double L = 9.0; int n = 1200; double h = 2 * L / n, s = -tval, sum = 0;
    double cs = 1.0 / (2 * M_PI * sqrt(1 - s * s));
    for (int i = 0; i <= n; i++) for (int j = 0; j <= n; j++)
    {
        double xx = -L + i * h, yy = -L + j * h, w = ((i == 0 || i == n) ? 0.5 : 1) * ((j == 0 || j == n) ? 0.5 : 1);
        arb_t x, y; acb_t t; arb_init(x); arb_init(y); acb_init(t);
        arb_set_d(x, xx); arb_set_d(y, yy); acb_set_d(t, tval);
        evalres E; evalres_init(&E); eval_point(&E, x, y, t);
        double u = arf_get_d(arb_midref(E.u), ARF_RND_NEAR), v = arf_get_d(arb_midref(E.v), ARF_RND_NEAR);
        double d = arf_get_d(arb_midref(acb_realref(E.dd)), ARF_RND_NEAR), R0 = arf_get_d(arb_midref(acb_realref(E.R0)), ARF_RND_NEAR);
        double r = 1 - d; r = sqrt(r > 0 ? r : 0); /* only for the sign-free quadratic form below we need r itself */
        acb_t rr; acb_init(rr); acb_poly_evaluate(rr, rho, t, prec); r = arf_get_d(arb_midref(acb_realref(rr)), ARF_RND_NEAR); acb_clear(rr);
        double phi3 = R0 / sqrt(d) * exp(-(u * u - 2 * r * u * v + v * v) / (2 * d));
        double dens = cs * exp(-(xx * xx - 2 * s * xx * yy + yy * yy) / (2 * (1 - s * s)));
        sum += w * phi3 * dens;
        arb_clear(x); arb_clear(y); acb_clear(t);
    }
    printf("T_{-t}[Phi_3] at t = %.4f (trapezoid, h = %.4f): %.12e\n", tval, h, sum * h * h);
}


/* ---------- exterior bound: max(|x|,|y|) > X0 ----------
   For |r| <= 1 one has A +- B >= 1/2, hence exp(-Re(Q/d)) <= exp(-(u^2+v^2)/2) <= exp(-s^2/4) e^{-(u^2+v^2)/4} with s = |u|+|v|
   ((u^2+v^2) >= s^2/2).  |l_u|, |l_v| <= s/delta, |1/d| <= 1/delta, |r| <= 1 give |F_ij| <= Ft_ij(s) (recurrence with absolute
   values), and Ft_ij(s) e^{-s^2/8} <= M_ij := sum_k c_k (4k/e)^{k/2}.  So |R_e|^2 exp(-Re(Q/d)) <= (sum_T c_T X_T(|x|) Y_T(|y|))^2,
   with X_T, Y_T Bell polynomials with absolute coefficients, and (sum_T a_T)^2 <= nT sum_T a_T^2.  Then
   J_e^ext <= (1/delta) nT sum_T c_T^2 [ m_ext(X_T^2) m(Y_T^2) + m(X_T^2) m_ext(Y_T^2) ],
   m(p) = int p(|x|) dgamma, m_ext(p) = int_{|x|>X0} p(|x|) dgamma, int_{|x|>X0} |x|^k dgamma = 2^{k/2} Gamma((k+1)/2, X0^2/2)/sqrt(pi).
   delta = min_{|t|=1} |1 - rho(t)^2| (rigorous, theta panels); kappa bounded with |t| = 1, |q_j| <= sum_k |c_k| k^j. */
static void moment_abs(arb_t out, slong k, const arb_t X0, int ext)
{
    /* int |x|^k dgamma over |x| > X0 (ext) or over R (X0 ignored) */
    arb_t a, z, pi; arb_init(a); arb_init(z); arb_init(pi);
    arb_set_ui(a, k + 1); arb_mul_2exp_si(a, a, -1);
    if (ext) { arb_sqr(z, X0, prec); arb_mul_2exp_si(z, z, -1); arb_hypgeom_gamma_upper(out, a, z, 0, prec); }
    else arb_gamma(out, a, prec);
    arb_const_pi(pi, prec); arb_sqrt(pi, pi, prec); arb_div(out, out, pi, prec);
    arb_set_ui(z, 2); arb_set_ui(a, k); arb_mul_2exp_si(a, a, -1); arb_pow(z, z, a, prec); arb_mul(out, out, z, prec);
    arb_clear(a); arb_clear(z); arb_clear(pi);
}
static void poly_abs(arb_poly_t out, const arb_poly_t p)
{ arb_poly_set(out, p); for (slong k = 0; k < arb_poly_length(out); k++) { arb_t c; arb_init(c); arb_abs(c, arb_poly_get_coeff_ptr(out, k)); arb_get_ubound_arf(arb_midref(c), c, prec); mag_zero(arb_radref(c)); arb_poly_set_coeff_arb(out, k, c); arb_clear(c); } }
static void poly_moment(arb_t out, const arb_poly_t p, const arb_t X0, int ext)
{ arb_zero(out); arb_t m; arb_init(m); for (slong k = 0; k < arb_poly_length(p); k++) { moment_abs(m, k, X0, ext); arb_addmul(out, m, arb_poly_get_coeff_ptr(p, k), prec); } arb_clear(m); }

static void exterior_bound(double X0d, double a_weight)
{
    arb_t X0, delta, tmp, th; arb_init(X0); arb_init(delta); arb_init(tmp); arb_init(th);
    arb_set_d(X0, X0d);
    /* delta = min |1 - rho^2| on the circle, 20000 theta panels */
    acb_t t, r; acb_init(t); acb_init(r); arf_t lb, mn; arf_init(lb); arf_init(mn); arf_pos_inf(mn);
    slong K = 20000;
    for (slong k = 0; k < K; k++)
    {
        set_interval(th, M_PI * k / K, M_PI * (k + 1) / K * (1 + 1e-15)); arb_sin_cos(acb_imagref(t), acb_realref(t), th, prec);
        acb_poly_evaluate(r, rho, t, prec); acb_sqr(r, r, prec); acb_sub_ui(r, r, 1, prec); acb_abs(tmp, r, prec);
        arb_get_lbound_arf(lb, tmp, prec); if (arf_cmp(lb, mn) < 0) arf_set(mn, lb);
    }
    arb_set_arf(delta, mn);
    printf("delta = min_{|t|=1} |1 - rho(t)^2| >= "); arf_printd(mn, 8); printf("\n");
    if (arf_sgn(mn) <= 0) { printf("delta not positive\n"); return; }
    /* |q_j| bounds and |kappa| bounds on |t| = 1 */
    arb_t Q[4]; for (int j = 0; j < 4; j++) { arb_init(Q[j]); for (slong k = 0; k < acb_poly_length(Drho[j]); k++) { acb_poly_get_coeff_acb(r, Drho[j], k); acb_abs(tmp, r, prec); arb_add(Q[j], Q[j], tmp, prec); } arb_get_ubound_arf(arb_midref(Q[j]), Q[j], prec); mag_zero(arb_radref(Q[j])); }
    arb_t kap[9]; for (int k = 0; k < 9; k++) arb_init(kap[k]);
    arb_set(kap[0], Q[3]); arb_mul(kap[1], Q[1], Q[2], prec); arb_mul_ui(kap[1], kap[1], 3, prec); arb_pow_ui(kap[2], Q[1], 3, prec);
    arb_one(kap[3]); arb_set_ui(kap[4], 3); arb_one(kap[5]); arb_add(kap[6], Q[1], Q[2], prec); arb_mul_ui(kap[6], kap[6], 3, prec);
    arb_sqr(kap[7], Q[1], prec); arb_mul_ui(kap[7], kap[7], 3, prec); arb_mul_ui(kap[8], Q[1], 3, prec);
    /* M_ij: Ft as polynomials in s with nonnegative coefficients */
    arb_poly_t Ft[4][4]; arb_t id; arb_init(id); arb_inv(id, delta, prec);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) arb_poly_init(Ft[i][j]);
    arb_poly_one(Ft[0][0]);
    arb_poly_t sx, tp; arb_poly_init(sx); arb_poly_init(tp); arb_poly_set_coeff_arb(sx, 1, id);   /* s/delta */
    for (int j = 1; j < 4; j++) { arb_poly_mul(Ft[0][j], sx, Ft[0][j - 1], prec); if (j >= 2) { arb_poly_scalar_mul(tp, Ft[0][j - 2], id, prec); arb_poly_scalar_mul_2exp_si(tp, tp, 0); for (int q = 0; q < j - 2; q++) {} arb_mul_ui(tmp, id, j - 1, prec); arb_poly_scalar_mul(tp, Ft[0][j - 2], tmp, prec); arb_poly_add(Ft[0][j], Ft[0][j], tp, prec); } }
    for (int i = 1; i < 4; i++) for (int j = 0; j < 4; j++)
    {
        arb_poly_mul(Ft[i][j], sx, Ft[i - 1][j], prec);
        if (i >= 2) { arb_mul_ui(tmp, id, i - 1, prec); arb_poly_scalar_mul(tp, Ft[i - 2][j], tmp, prec); arb_poly_add(Ft[i][j], Ft[i][j], tp, prec); }
        if (j >= 1) { arb_mul_ui(tmp, id, j, prec); arb_poly_scalar_mul(tp, Ft[i - 1][j - 1], tmp, prec); arb_poly_add(Ft[i][j], Ft[i][j], tp, prec); }
    }
    arb_t M[4][4];
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++)
    {
        arb_init(M[i][j]);
        for (slong k = 0; k < arb_poly_length(Ft[i][j]); k++)
        {
            arb_t c; arb_init(c);
            if (k == 0) arb_one(c); else { arb_set_ui(c, 4 * k); { arb_t ee; arb_init(ee); arb_const_e(ee, prec); arb_div(c, c, ee, prec); arb_clear(ee); } arb_set_ui(tmp, k); arb_mul_2exp_si(tmp, tmp, -1); arb_pow(c, c, tmp, prec); }
            arb_addmul(M[i][j], c, arb_poly_get_coeff_ptr(Ft[i][j], k), prec); arb_clear(c);
        }
    }
    /* terms T = (kappa_k, i, j) for each e: c_T = |kappa_k| M_ij, X_T = |B_{a+e,i}|, Y_T = |B_{a+e,j}| */
    static const int PA[9][2] = { {1,0},{2,0},{3,0},{0,1},{0,2},{0,3},{1,1},{2,1},{1,2} };
    arb_t S[2], mx, my, mxe, mye, cT; arb_init(S[0]); arb_init(S[1]); arb_init(mx); arb_init(my); arb_init(mxe); arb_init(mye); arb_init(cT);
    arb_poly_t Xa, X2; arb_poly_init(Xa); arb_poly_init(X2);
    for (int e = 0; e < 2; e++)
    {
        slong nT = 0;
        for (int k = 0; k < 9; k++) { int p = PA[k][0], a = PA[k][1], aa = a + e; for (int i = 0; i <= aa; i++) for (int j = 0; j <= aa; j++) { if (p == 0 && (i == 0 || j == 0)) continue; if (arb_poly_is_zero(Bell[aa][i]) || arb_poly_is_zero(Bell[aa][j])) continue; nT++; } }
        for (int k = 0; k < 9; k++)
        {
            int p = PA[k][0], a = PA[k][1], aa = a + e;
            for (int i = 0; i <= aa; i++) for (int j = 0; j <= aa; j++)
            {
                int fi, fj;
                if (p >= 1) { fi = i + p - 1; fj = j + p - 1; } else { if (i == 0 || j == 0) continue; fi = i - 1; fj = j - 1; }
                if (arb_poly_is_zero(Bell[aa][i]) || arb_poly_is_zero(Bell[aa][j])) continue;
                arb_mul(cT, kap[k], M[fi][fj], prec);
                poly_abs(Xa, Bell[aa][i]); arb_poly_mul(X2, Xa, Xa, prec); poly_moment(mx, X2, X0, 0); poly_moment(mxe, X2, X0, 1);
                poly_abs(Xa, Bell[aa][j]); arb_poly_mul(X2, Xa, Xa, prec); poly_moment(my, X2, X0, 0); poly_moment(mye, X2, X0, 1);
                arb_mul(tmp, mxe, my, prec); arb_addmul(tmp, mx, mye, prec); arb_mul(tmp, tmp, cT, prec); arb_mul(tmp, tmp, cT, prec);
                arb_add(S[e], S[e], tmp, prec);
            }
        }
        arb_mul_ui(S[e], S[e], nT, prec); arb_mul(S[e], S[e], id, prec);
        printf("exterior (max(|x|,|y|) > %.1f): J_%d^ext <= ", X0d, e); arb_printd(S[e], 6); printf("   (%ld terms)\n", nT);
    }
    (void) a_weight;
}

int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "usage: d3norm SCHEME X0 eta tau maxboxes | d3norm SCHEME test t\n"); return 2; }
    setup_scheme(argv[1]);
    if (strcmp(argv[2], "test") == 0) { test_mode(atof(argv[3])); return 0; }
    if (strcmp(argv[2], "ext") == 0) { exterior_bound(atof(argv[3]), 0); return 0; }
    if (strcmp(argv[2], "probe2") == 0)
    {
        double xs = atof(argv[3]), ys = atof(argv[4]), ts = atof(argv[5]), w = atof(argv[6]), e = 1e-5;
        double cv[2], ub[2]; eval_box(cv, xs, xs, ys, ys, ts, ts);
        eval_box(ub, xs, xs + w, ys, ys + e, ts, ts + e); printf("x only : %.3e %.3e\n", ub[0] / cv[0], ub[1] / cv[1]);
        eval_box(ub, xs, xs + e, ys, ys + w, ts, ts + e); printf("y only : %.3e %.3e\n", ub[0] / cv[0], ub[1] / cv[1]);
        eval_box(ub, xs, xs + e, ys, ys + e, ts, ts + w); printf("th only: %.3e %.3e\n", ub[0] / cv[0], ub[1] / cv[1]);
        return 0;
    }
    if (strcmp(argv[2], "probe") == 0)
    {
        double xs = atof(argv[3]), ys = atof(argv[4]), ts = atof(argv[5]);
        for (double w = 0.4; w > 1e-4; w /= 4)
        { double ub[2], cv[2]; eval_box(ub, xs, xs + w, ys, ys + w, ts, ts + w / 2); double xm = xs + w / 2, ym = ys + w / 2, tm = ts + w / 4; eval_box(cv, xm, xm, ym, ym, tm, tm);
          printf("w = %.5f  ub/center: J0 %.3e  J1 %.3e   (center %.3e %.3e)\n", w, ub[0] / cv[0], ub[1] / cv[1], cv[0], cv[1]); }
        return 0;
    }
    double X0 = atof(argv[2]), eta = atof(argv[3]), tau = atof(argv[4]); long maxboxes = atol(argv[5]);
    printf("P(x) = "); arb_poly_printd(Pm, 12); printf("\nrho(t) = "); acb_poly_printd(rho, 12); printf("\n");

    /* adaptive partition: stack of boxes */
    typedef struct { double x0, x1, y0, y1, t0, t1; } box_t;
    long cap = 1 << 24; box_t *stk = malloc(sizeof(box_t) * cap); long sp = 0;
    int nx = 16, ny = 32, nt = 32;
    for (int i = 0; i < nx; i++) for (int j = 0; j < ny; j++) for (int k = 0; k < nt; k++)
    { box_t b = { X0 * i / nx, X0 * (i + 1) / nx, -X0 + 2 * X0 * j / ny, -X0 + 2 * X0 * (j + 1) / ny, M_PI * k / nt, M_PI * (k + 1) / nt };
      if (k == nt - 1) b.t1 = M_PI;   /* t1 is enlarged to cover pi below */
      stk[sp++] = b; }
    double J[2] = {0, 0}, Jc[2] = {0, 0}; long nacc = 0, neval = 0;
    double pi_up = 3.14159265358979323846 * (1 + 1e-15);
    while (sp > 0)
    {
        box_t b = stk[--sp];
        double t1 = (b.t1 >= M_PI) ? pi_up : b.t1;
        double ub[2], cv[2]; eval_box(ub, b.x0, b.x1, b.y0, b.y1, b.t0, t1); neval++;
        double vol = (b.x1 - b.x0) * (b.y1 - b.y0) * (t1 - b.t0) * (1 + 1e-12);
        double xm = 0.5 * (b.x0 + b.x1), ym = 0.5 * (b.y0 + b.y1), tm = 0.5 * (b.t0 + t1);
        eval_box(cv, xm, xm, ym, ym, tm, tm);
        double excess = (ub[0] - cv[0]) + (ub[1] - cv[1]);
        int accept = (excess * vol <= eta * (cv[0] + cv[1]) * vol + tau * vol) || (sp + 2 >= cap) || (neval > maxboxes);
        if (!accept && !(ub[0] < INFINITY && ub[1] < INFINITY)) accept = 0;
        if (accept)
        {
            if (!(ub[0] < INFINITY) || !(ub[1] < INFINITY)) { printf("infinite bound on an accepted box; increase maxboxes\n"); return 1; }
            for (int e = 0; e < 2; e++) { J[e] += ub[e] * vol; Jc[e] += cv[e] * vol; }
            nacc++;
        }
        else
        {
            /* split the dimension with the largest scaled width */
            double wx = (b.x1 - b.x0) / 0.25, wy = (b.y1 - b.y0) / 0.25, wt = (b.t1 - b.t0) / 0.1;
            box_t c1 = b, c2 = b;
            if (wx >= wy && wx >= wt) { double m = 0.5 * (b.x0 + b.x1); c1.x1 = m; c2.x0 = m; }
            else if (wy >= wt) { double m = 0.5 * (b.y0 + b.y1); c1.y1 = m; c2.y0 = m; }
            else { double m = 0.5 * (b.t0 + b.t1); c1.t1 = m; c2.t0 = m; }
            stk[sp++] = c1; stk[sp++] = c2;
        }
        if (neval % 2000000 == 0) fprintf(stderr, "evals %ld accepted %ld stack %ld  J0 <= %.6f J1 <= %.6f\n", neval, nacc, sp, 2 * J[0] / M_PI, 2 * J[1] / M_PI);
    }
    /* symmetry factor 2, mean over theta: 1/pi; outward safety */
    double J0 = 2 * J[0] / M_PI * (1 + 1e-9), J1 = 2 * J[1] / M_PI * (1 + 1e-9);
    printf("boxes accepted %ld, evaluations %ld\n", nacc, neval);
    printf("inner domain [0,%.1f]x[-%.1f,%.1f]x[0,pi]:  J0 <= %.9e   J1 <= %.9e   (center-value sums %.6e, %.6e)\n", X0, X0, X0, J0, J1, 2 * Jc[0] / M_PI, 2 * Jc[1] / M_PI);
    return 0;
}
