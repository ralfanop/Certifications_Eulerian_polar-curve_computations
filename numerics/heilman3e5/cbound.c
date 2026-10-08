/*
  cbound.c -- rigorous a priori bound  M' >= sup_{|zeta| = rho'} |E(sin zeta)|,  E = H - arcsin,
  from the integral representation (valid for z in the strip where the margins below are > 0)

     E(z) = (pi/2) int int p_z(u,v) D(a(u), b(v); z) du dv,
     p_z(u,v) = exp(-Q_z(u,v)) / (pi sqrt(1-z^2)),   Q_z(u,v) = (u^2 + v^2 - 2 z u v)/(1 - z^2),
     D(a,b;z) = erf(a) erf(b) + 2 int_0^z [p_t(a,b) - p_t(0,0)] dt.

  With w_t = 1/(1-t^2) and m(t) = Re w_t - |Re(t w_t)| > 0 on the segment [0,z], Re Q_t(a,b) >= 0, so
     |p_t(a,b) - p_t(0,0)| <= |c_t| min(2, |w_t| (a^2+b^2) + 2 |t w_t| |a||b|),  c_t = 1/(pi sqrt(1-t^2)),
     |D| <= |erf a||erf b| + 2 |z| Ct min(2, Wt (a^2+b^2) + 2 TWt |a||b|) =: Dbd(|a|,|b|),
  with Ct, Wt, TWt suprema over the segment.  Then
     |E(z)| <= (pi/2) [ sum_cells area |c_z| exp(-min_cell Re Q_z) Dbd(sup|a|, sup|b|)
                        + |c_z| Dmax (pi/m_z) 2 erfc(U sqrt(m_z)) ],   Dmax = 1 + 4|z| Ct,
  the last term covering max(|u|,|v|) > U (Re Q_z >= m_z (u^2+v^2)).
  The integrand bound is symmetric under (u,v) -> (-u,-v) (a, b odd): cells with u >= 0, doubled.

  usage: cbound profile_A profile_B rho' K U h prec
*/
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/arb_hypgeom.h>

#define NMODES 51
#define MAXDEG 101
#define NSEG 1024
static slong prec;
static arb_ptr sq_a, sq_b;

static void psi_vec(acb_ptr out, const acb_t x, slong nmax)
{
    acb_one(out);
    if (nmax >= 1) acb_mul_arb(out + 1, x, sq_a + 0, prec);
    for (slong n = 1; n < nmax; n++)
    {
        acb_t t; acb_init(t);
        acb_mul(t, x, out + n, prec); acb_mul_arb(t, t, sq_a + n, prec);
        acb_submul_arb(t, out + n - 1, sq_b + n, prec);
        acb_swap(out + n + 1, t); acb_clear(t);
    }
}

/* sup |a| on the real interval [lo,hi] via midpoint value + Taylor deviation bound */
static double sup_abs_profile(arb_t *Ac, double lo, double hi)
{
    acb_t c0, a0; acb_init(c0); acb_init(a0);
    arb_set_d(acb_realref(c0), 0.5 * (lo + hi)); arb_zero(acb_imagref(c0));
    mag_t r, ra, Mx, cur, dv, tm; mag_init(r); mag_init(ra); mag_init(Mx); mag_init(cur); mag_init(dv); mag_init(tm);
    mag_set_d(r, 0.5 * (hi - lo) * (1 + 1e-12) + 1e-300);
    acb_ptr p = _acb_vec_init(MAXDEG + 1); psi_vec(p, c0, MAXDEG);
    acb_zero(a0); mag_zero(ra); mag_zero(Mx);
    int j = 0;
    for (slong k = 0; k <= MAXDEG; k++)
    {
        acb_get_mag(cur, p + k); mag_max(Mx, Mx, cur);
        if (j < NMODES && k == 2 * j + 1)
        {
            acb_addmul_arb(a0, p + k, Ac[j], prec);
            mag_set_ui(dv, 2 * k); mag_sqrt(dv, dv); mag_mul(dv, dv, r); mag_expm1(dv, dv); mag_mul(dv, dv, Mx);
            arb_get_mag(tm, Ac[j]); mag_mul(tm, tm, dv); mag_add(ra, ra, tm); j++;
        }
    }
    acb_get_mag(cur, a0); mag_add(cur, cur, ra);
    double res = mag_get_d(cur) * (1 + 1e-12);   /* mag_get_d is an upper bound up to rounding; widen */
    _acb_vec_clear(p, MAXDEG + 1);
    acb_clear(c0); acb_clear(a0); mag_clear(r); mag_clear(ra); mag_clear(Mx); mag_clear(cur); mag_clear(dv); mag_clear(tm);
    return res;
}

static void load_profile(arb_t *Ac, const char *fn)
{
    arb_t pi, q; arb_init(pi); arb_init(q); arb_const_pi(pi, prec); arb_root_ui(q, pi, 4, prec); arb_inv(q, q, prec);
    FILE *f = fopen(fn, "r"); char buf[128];
    for (int j = 0; j < NMODES; j++) { if (fscanf(f, "%127s", buf) != 1) exit(1); arb_init(Ac[j]); arb_set_str(Ac[j], buf, prec); arb_mul(Ac[j], Ac[j], q, prec); }
    fclose(f); arb_clear(pi); arb_clear(q);
}

int main(int argc, char **argv)
{
    const char *fa = argv[1], *fb = argv[2]; const char *rhos = argv[3]; slong K = atol(argv[4]);
    double U = atof(argv[5]), h = atof(argv[6]); prec = atol(argv[7]);
    sq_a = _arb_vec_init(MAXDEG + 2); sq_b = _arb_vec_init(MAXDEG + 2);
    for (slong n = 0; n <= MAXDEG + 1; n++)
    {
        arb_set_ui(sq_a + n, 2); arb_div_ui(sq_a + n, sq_a + n, n + 1, prec); arb_sqrt(sq_a + n, sq_a + n, prec);
        arb_set_ui(sq_b + n, n); arb_div_ui(sq_b + n, sq_b + n, n + 1, prec); arb_sqrt(sq_b + n, sq_b + n, prec);
    }
    arb_t Aa[NMODES], Ab[NMODES]; load_profile(Aa, fa); load_profile(Ab, fb);

    slong nu = (slong) llround(U / h), nv = 2 * nu;
    double *Aub = malloc(sizeof(double) * nu), *Bub = malloc(sizeof(double) * nv), *Ea = malloc(sizeof(double) * nu), *Eb = malloc(sizeof(double) * nv);
    arb_t x; arb_init(x);
    for (slong i = 0; i < nu; i++)
    {
        Aub[i] = sup_abs_profile(Aa, i * h, (i + 1) * h);
        arb_set_d(x, Aub[i]); arb_hypgeom_erf(x, x, prec);
        { mag_t mg; mag_init(mg); arb_get_mag(mg, x); Ea[i] = fmin(1.0, mag_get_d(mg) * (1 + 1e-12)); mag_clear(mg); }
    }
    for (slong i = 0; i < nv; i++)
    {
        double lo = -U + i * h, hi = lo + h;
        double alo = fmax(0, fmin(fabs(lo), fabs(hi)) - 0), ahi = fmax(fabs(lo), fabs(hi));
        if (lo < 0 && hi > 0) alo = 0;
        /* b odd: sup over [lo,hi] = sup over [alo, ahi] mirrored when the cell lies on one side */
        Bub[i] = sup_abs_profile(Ab, alo, ahi);
        arb_set_d(x, Bub[i]); arb_hypgeom_erf(x, x, prec);
        { mag_t mg; mag_init(mg); arb_get_mag(mg, x); Eb[i] = fmin(1.0, mag_get_d(mg) * (1 + 1e-12)); mag_clear(mg); }
    }
    fprintf(stderr, "profile bounds done: sup|a| on [0,h] %.3e, on last cell %.3e\n", Aub[0], Aub[nu - 1]);

    arb_t rho; arb_init(rho); arb_set_str(rho, rhos, prec);
    double Mmax = 0, minmargin = 1e9, maxRe = 0;
    acb_t zeta, z, w, tw, t, c, one; acb_init(zeta); acb_init(z); acb_init(w); acb_init(tw); acb_init(t); acb_init(c); acb_init(one);
    arb_t th, rad, a, b, tmp; arb_init(th); arb_init(rad); arb_init(a); arb_init(b); arb_init(tmp);
    for (slong j = 0; j < K; j++)
    {
        /* zeta = rho e^{i theta}, theta in the ball covering [pi/2 j/K, pi/2 (j+1)/K] */
        arb_const_pi(th, prec); arb_mul_ui(th, th, 2 * j + 1, prec); arb_div_ui(th, th, 4 * K, prec);
        arb_const_pi(rad, prec); arb_div_ui(rad, rad, 4 * K, prec); arb_add_error(th, rad);
        arb_sin_cos(b, a, th, prec);
        arb_mul(a, a, rho, prec); arb_mul(b, b, rho, prec);
        acb_set_arb_arb(zeta, a, b);
        acb_sin(z, zeta, prec);
        { mag_t mg; mag_init(mg); arb_get_mag(mg, acb_realref(z)); if (mag_get_d(mg) > maxRe) maxRe = mag_get_d(mg); mag_clear(mg); }
        /* segment [0, z]: 64 pieces of s */
        double Ct = 0, Wt = 0, TWt = 0, mseg = 1e9;
        for (int q = 0; q < NSEG; q++)
        {
            arb_t s; arb_init(s); arb_set_d(s, (q + 0.5) / (double) NSEG); mag_set_d(arb_radref(s), 0.5 / (double) NSEG * (1 + 1e-12));
            acb_mul_arb(t, z, s, prec);
            acb_sqr(w, t, prec); acb_one(one); acb_sub(w, one, w, prec);           /* 1 - t^2 */
            acb_sqrt(c, w, prec); acb_inv(w, w, prec);                                /* w_t */
            acb_mul(tw, t, w, prec);
            /* margin m = Re w - |Re tw| (lower bound) */
            arb_abs(tmp, acb_realref(tw)); arb_sub(tmp, acb_realref(w), tmp, prec);
            { arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, tmp, prec); double m = arf_get_d(lb, ARF_RND_DOWN); if (m < mseg) mseg = m; arf_clear(lb); }
            mag_t mg; mag_init(mg);
            acb_get_mag(mg, w); if (mag_get_d(mg) > Wt) Wt = mag_get_d(mg);
            acb_get_mag(mg, tw); if (mag_get_d(mg) > TWt) TWt = mag_get_d(mg);
            /* |c_t| = 1/(pi |sqrt(1-t^2)|) <= 1/(pi * lower|sqrt|) */
            { arb_t ab; arb_init(ab); acb_abs(ab, c, prec); arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, ab, prec);
              double cl = arf_get_d(lb, ARF_RND_DOWN); double ct = 1.0 / (M_PI * cl) * (1 + 1e-12); if (cl <= 0) ct = INFINITY; if (ct > Ct) Ct = ct; arf_clear(lb); arb_clear(ab); }
            mag_clear(mg); arb_clear(s);
        }
        Wt *= (1 + 1e-12); TWt *= (1 + 1e-12);
        /* z itself */
        acb_sqr(w, z, prec); acb_one(one); acb_sub(w, one, w, prec); acb_sqrt(c, w, prec); acb_inv(w, w, prec); acb_mul(tw, z, w, prec);
        arf_t lb; arf_init(lb);
        arb_get_lbound_arf(lb, acb_realref(w), prec); double alo = arf_get_d(lb, ARF_RND_DOWN);
        double bhi, blo; { arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, acb_realref(tw), prec); bhi = arf_get_d(ub, ARF_RND_UP); arb_get_lbound_arf(ub, acb_realref(tw), prec); blo = arf_get_d(ub, ARF_RND_DOWN); arf_clear(ub); }
        double mz = alo - fmax(fabs(bhi), fabs(blo));
        double cz; { arb_t ab; arb_init(ab); acb_abs(ab, c, prec); arb_get_lbound_arf(lb, ab, prec); cz = 1.0 / (M_PI * arf_get_d(lb, ARF_RND_DOWN)) * (1 + 1e-12); arb_clear(ab); }
        double zabs; { mag_t mg; mag_init(mg); acb_get_mag(mg, z); zabs = mag_get_d(mg) * (1 + 1e-12); mag_clear(mg); }
        arf_clear(lb);
        if (mseg < minmargin) minmargin = mseg; if (mz < minmargin) minmargin = mz;
        if (mseg <= 0 || mz <= 0) { printf("margin failure at arc %ld (mseg %g mz %g alo %g blo %g bhi %g)\n", j, mseg, mz, alo, blo, bhi); acb_printn(z, 10, 0); printf("\n"); return 1; }
        /* cell sum (doubles with conservative rounding: every factor is an upper bound; final x(1+1e-9)) */
        double sum = 0;
        for (slong iu = 0; iu < nu; iu++)
        {
            double u0 = iu * h, u1 = u0 + h;
            for (slong iv = 0; iv < nv; iv++)
            {
                double v0 = -U + iv * h, v1 = v0 + h;
                double vmin2 = (v0 < 0 && v1 > 0) ? 0 : fmin(v0 * v0, v1 * v1);
                double uv[4] = { u0 * v0, u0 * v1, u1 * v0, u1 * v1 };
                double uvlo = fmin(fmin(uv[0], uv[1]), fmin(uv[2], uv[3])), uvhi = fmax(fmax(uv[0], uv[1]), fmax(uv[2], uv[3]));
                /* max of beta*uv over beta in [blo,bhi], uv in [uvlo,uvhi] */
                double bm = fmax(fmax(blo * uvlo, blo * uvhi), fmax(bhi * uvlo, bhi * uvhi));
                double reQ = alo * (u0 * u0 + vmin2) - 2 * bm;
                reQ = reQ * (reQ > 0 ? (1 - 1e-12) : (1 + 1e-12)) - 1e-12;
                double A = Aub[iu], B = Bub[iv];
                double inner = Wt * (A * A + B * B) + 2 * TWt * A * B;
                double D = Ea[iu] * Eb[iv] + 2 * zabs * Ct * fmin(2.0, inner);
                sum += h * h * cz * exp(-reQ) * D;
            }
        }
        sum *= 2 * (1 + 1e-9);
        double Dmax = 1 + 4 * zabs * Ct;
        double outer = cz * Dmax * (M_PI / mz) * 2 * erfc(U * sqrt(mz)) * (1 + 1e-9) + 1e-300;
        double Mz = (M_PI / 2) * (sum + outer) * (1 + 1e-9);
        if (Mz > Mmax) Mmax = Mz;
        if (j % (K / 20) == 0) fprintf(stderr, "arc %ld/%ld  |z|<=%.4f  margin %.4f  inner %.4e outer %.2e  bound %.5f\n", j, K, zabs, fmin(mz, mseg), sum, outer, Mz);
    }
    printf("rho' = %s: sup |E(sin zeta)| <= %.6f  (min margin %.4f, max |Re sin zeta| <= %.6f)\n", rhos, Mmax * (1 + 1e-6), minmargin, maxRe);
    return 0;
}
