/* fibcore.h -- exact ball enclosure of the priced threshold functional
 *
 *   J(c, a) = E[(|p_a(Z)| - c|Z|)_+],   p_a = a0 psi0 + a1 psi1 + a2 psi2 + a3 psi3,   Z ~ N(0,1),
 *
 * psi_j the orthonormal Hermite polynomials (psi2 = (z^2-1)/sqrt2, psi3 = (z^3-3z)/sqrt6).
 * Writing p(z) = P0 + P1 z + P2 z^2 + P3 z^3 and r_{1,2}(z) = p(z) -/+ c z,
 *
 *   J = int_0^inf [ (r1)_+ + (-r2)_+ ] phi + int_{-inf}^0 [ (r2)_+ + (-r1)_+ ] phi .
 *
 * Each term is integrated in closed form: the real roots of r are isolated rigorously (acb_poly_find_roots,
 * acb_poly_validate_real_roots, plus a sign change across every real root interval), the sign of r on each gap
 * between root intervals is certified at an interior point, and int_a^b z^k phi is given by the Gaussian moment
 * recursion.  The (tiny) root intervals themselves are charged with width * phi0 * sup|r|.  The result is a
 * rigorous UPPER bound (returned as an arb whose upper endpoint is used).
 */
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/arb_poly.h>
#include <flint/acb_poly.h>
#include <flint/arb_hypgeom.h>

static arb_t C_RSQ2, C_RSQ6, C_PHI0, C_NU;  /* 1/sqrt2, 1/sqrt6, 1/sqrt(2pi), sqrt(2/pi) */

static void fib_init(slong prec)
{
    arb_init(C_RSQ2); arb_init(C_RSQ6); arb_init(C_PHI0); arb_init(C_NU);
    arb_set_ui(C_RSQ2, 2); arb_rsqrt(C_RSQ2, C_RSQ2, prec);
    arb_set_ui(C_RSQ6, 6); arb_rsqrt(C_RSQ6, C_RSQ6, prec);
    arb_const_pi(C_PHI0, prec); arb_mul_2exp_si(C_PHI0, C_PHI0, 1); arb_rsqrt(C_PHI0, C_PHI0, prec);
    arb_mul_2exp_si(C_NU, C_PHI0, 1);
}

/* phi(x) and the upper tail Q(x) = P(Z > x) */
static void gphi(arb_t r, const arb_t x, slong prec)
{
    arb_t t; arb_init(t); arb_sqr(t, x, prec); arb_mul_2exp_si(t, t, -1); arb_neg(t, t); arb_exp(t, t, prec);
    arb_mul(r, t, C_PHI0, prec); arb_clear(t);
}
static void gtail(arb_t r, const arb_t x, slong prec)
{
    arb_t t; arb_init(t); arb_mul(t, x, C_RSQ2, prec); arb_hypgeom_erfc(t, t, prec); arb_mul_2exp_si(r, t, -1); arb_clear(t);
}

/* I_k = int_a^b z^k phi(z) dz, k = 0..3; ainf = -1 means a = -inf, binf = +1 means b = +inf */
static void gmom(arb_ptr I, const arb_t a, int ainf, const arb_t b, int binf, slong prec)
{
    arb_t pa, pb, Qa, Qb, t; arb_init(pa); arb_init(pb); arb_init(Qa); arb_init(Qb); arb_init(t);
    if (ainf) { arb_zero(pa); arb_one(Qa); } else { gphi(pa, a, prec); gtail(Qa, a, prec); }
    if (binf) { arb_zero(pb); arb_zero(Qb); } else { gphi(pb, b, prec); gtail(Qb, b, prec); }
    arb_sub(I + 0, Qa, Qb, prec);
    arb_sub(I + 1, pa, pb, prec);
    /* I2 = I0 + a phi(a) - b phi(b),  I3 = 2 I1 + a^2 phi(a) - b^2 phi(b) */
    arb_set(I + 2, I + 0); arb_mul_2exp_si(I + 3, I + 1, 1);
    if (!ainf) { arb_mul(t, a, pa, prec); arb_add(I + 2, I + 2, t, prec); arb_mul(t, t, a, prec); arb_add(I + 3, I + 3, t, prec); }
    if (!binf) { arb_mul(t, b, pb, prec); arb_sub(I + 2, I + 2, t, prec); arb_mul(t, t, b, prec); arb_sub(I + 3, I + 3, t, prec); }
    arb_clear(pa); arb_clear(pb); arb_clear(Qa); arb_clear(Qb); arb_clear(t);
}

/* real root intervals of the real cubic (or lower degree) r = q[0..3]; returns count, -1 on failure */
static int real_roots(arf_ptr lo, arf_ptr hi, arb_srcptr q, slong prec)
{
    int deg = 3; while (deg >= 0 && arb_is_zero(q + deg)) deg--;
    if (deg <= 0) return 0;
    if (arb_contains_zero(q + deg)) return -1;
    acb_poly_t P; acb_ptr R; acb_poly_init(P); R = _acb_vec_init(deg);
    for (int k = 0; k <= deg; k++) { acb_t z; acb_init(z); acb_set_arb(z, q + k); acb_poly_set_coeff_acb(P, k, z); acb_clear(z); }
    int n = 0, ok = 0;
    for (slong p = prec; p <= 4 * prec && !ok; p *= 2)
    {
        slong iso = acb_poly_find_roots(R, P, NULL, 0, p);
        if (iso == deg && acb_poly_validate_real_roots(R, P, p)) ok = 1;
    }
    if (ok)
    {
        arb_t v; arb_init(v);
        for (int k = 0; k < deg && ok; k++)
        {
            if (!arb_contains_zero(acb_imagref(R + k))) continue;
            arf_t l, h; arf_init(l); arf_init(h);
            arb_get_lbound_arf(l, acb_realref(R + k), prec); arb_get_ubound_arf(h, acb_realref(R + k), prec);
            /* independent check: strict sign change across the interval (IVT) */
            arb_t x, rl, rh; arb_init(x); arb_init(rl); arb_init(rh);
            arb_poly_t Q; arb_poly_init(Q); for (int j = 0; j <= deg; j++) arb_poly_set_coeff_arb(Q, j, q + j);
            int sc = 0;
            for (int w = 0; w < 4 && !sc; w++)
            {
                if (w > 0) { /* widen an (almost) exact root interval: delta = 2^-(120-20w) (1 + |endpoint|) */
                    arf_t dl; arf_init(dl); arf_abs(dl, l); arf_add_ui(dl, dl, 1, 30, ARF_RND_UP); arf_mul_2exp_si(dl, dl, -(120 - 20 * w));
                    arf_sub(l, l, dl, prec, ARF_RND_DOWN); arf_abs(dl, h); arf_add_ui(dl, dl, 1, 30, ARF_RND_UP); arf_mul_2exp_si(dl, dl, -(120 - 20 * w));
                    arf_add(h, h, dl, prec, ARF_RND_UP); arf_clear(dl); }
                arb_set_arf(x, l); arb_poly_evaluate(rl, Q, x, prec); arb_set_arf(x, h); arb_poly_evaluate(rh, Q, x, prec);
                sc = (arb_is_positive(rl) && arb_is_negative(rh)) || (arb_is_negative(rl) && arb_is_positive(rh));
            }
            if (!sc) ok = 0;
            arf_set(lo + n, l); arf_set(hi + n, h); n++;
            arb_poly_clear(Q); arb_clear(x); arb_clear(rl); arb_clear(rh); arf_clear(l); arf_clear(h);
        }
        arb_clear(v);
    }
    _acb_vec_clear(R, deg); acb_poly_clear(P);
    if (!ok) return -1;
    /* independent count of the real roots from the discriminant (exact count needs a certain sign):
       n disjoint intervals, each with a certified sign change, and exactly n real roots in total
       => every real root lies in one of the intervals, whatever the root finder did */
    {
        arb_t D, t; arb_init(D); arb_init(t); int cnt = -1;
        if (deg == 1) cnt = 1;
        else if (deg == 2) { arb_sqr(D, q + 1, prec); arb_mul(t, q + 2, q + 0, prec); arb_mul_2exp_si(t, t, 2); arb_sub(D, D, t, prec);
            if (arb_is_positive(D)) cnt = 2; else if (arb_is_negative(D)) cnt = 0; }
        else {
            /* a = q3, b = q2, c = q1, d = q0:  18abcd - 4b^3 d + b^2 c^2 - 4 a c^3 - 27 a^2 d^2 */
            arb_srcptr a = q + 3, b = q + 2, c = q + 1, d = q + 0;
            arb_mul(t, a, b, prec); arb_mul(t, t, c, prec); arb_mul(t, t, d, prec); arb_mul_ui(D, t, 18, prec);
            arb_pow_ui(t, b, 3, prec); arb_mul(t, t, d, prec); arb_mul_ui(t, t, 4, prec); arb_sub(D, D, t, prec);
            arb_mul(t, b, c, prec); arb_sqr(t, t, prec); arb_add(D, D, t, prec);
            arb_pow_ui(t, c, 3, prec); arb_mul(t, t, a, prec); arb_mul_ui(t, t, 4, prec); arb_sub(D, D, t, prec);
            arb_mul(t, a, d, prec); arb_sqr(t, t, prec); arb_mul_ui(t, t, 27, prec); arb_sub(D, D, t, prec);
            if (arb_is_positive(D)) cnt = 3; else if (arb_is_negative(D)) cnt = 1; }
        arb_clear(D); arb_clear(t);
        if (cnt != n) return -1;
    }
    /* sort by lower endpoint */
    for (int i = 1; i < n; i++) for (int j = i; j > 0 && arf_cmp(lo + j, lo + j - 1) < 0; j--) { arf_swap(lo + j, lo + j - 1); arf_swap(hi + j, hi + j - 1); }
    for (int i = 1; i < n; i++) if (arf_cmp(lo + i, hi + i - 1) <= 0) return -1;   /* must be disjoint */
    return n;
}

/* upper bound of int over the half-line (side = +1: (0,inf), side = -1: (-inf,0)) of (s * r(z))_+ phi(z) dz.
   returns 0 on success, -1 on failure */
static int half_posint(arb_t res, arb_srcptr q, int s, int side, slong prec)
{
    arf_struct lo[3], hi[3]; for (int i = 0; i < 3; i++) { arf_init(lo + i); arf_init(hi + i); }
    int n = real_roots(lo, hi, q, prec);
    if (n < 0) { for (int i = 0; i < 3; i++) { arf_clear(lo + i); arf_clear(hi + i); } return -1; }
    /* uncertain intervals clipped to the closed half-line */
    arf_struct ul[3], uh[3]; int m = 0;
    for (int i = 0; i < 3; i++) { arf_init(ul + i); arf_init(uh + i); }
    for (int i = 0; i < n; i++)
    {
        if (side > 0 && arf_sgn(hi + i) < 0) continue;
        if (side < 0 && arf_sgn(lo + i) > 0) continue;
        arf_set(ul + m, lo + i); arf_set(uh + m, hi + i);
        if (side > 0 && arf_sgn(ul + m) < 0) arf_zero(ul + m);
        if (side < 0 && arf_sgn(uh + m) > 0) arf_zero(uh + m);
        m++;
    }
    arb_poly_t Q; arb_poly_init(Q); for (int j = 0; j <= 3; j++) arb_poly_set_coeff_arb(Q, j, q + j);
    arb_t a, b, x, v, t, I[4]; arb_init(a); arb_init(b); arb_init(x); arb_init(v); arb_init(t);
    for (int k = 0; k < 4; k++) arb_init(I[k]);
    arb_zero(res); int fail = 0;
    /* gaps: endpoints e_0 = boundary, then (uh_{i-1}, ul_i), ..., last to infinity */
    for (int g = 0; g <= m && !fail; g++)
    {
        int ainf = 0, binf = 0;
        if (side > 0) {
            if (g == 0) arb_zero(a); else arb_set_arf(a, uh + g - 1);
            if (g == m) binf = 1; else arb_set_arf(b, ul + g);
        } else {
            if (g == 0) ainf = -1; else arb_set_arf(a, uh + g - 1);
            if (g == m) arb_zero(b); else arb_set_arf(b, ul + g);
        }
        if (!ainf && !binf && arb_ge(a, b)) continue;   /* empty gap */
        /* interior point */
        if (ainf) { arb_sub_ui(x, b, 1, prec); }
        else if (binf) { arb_add_ui(x, a, 1, prec); }
        else { arb_add(x, a, b, prec); arb_mul_2exp_si(x, x, -1); }
        arb_poly_evaluate(v, Q, x, prec); if (s < 0) arb_neg(v, v);
        if (arb_is_negative(v)) continue;
        if (!arb_is_positive(v)) { fail = 1; break; }
        gmom(I[0], a, ainf, b, binf, prec);
        arb_zero(t); for (int k = 0; k < 4; k++) arb_addmul(t, q + k, I[k], prec);
        if (s < 0) arb_neg(t, t);
        arb_add(res, res, t, prec);
    }
    /* charge the root intervals: width * phi0 * sup |r| */
    for (int i = 0; i < m && !fail; i++)
    {
        arb_set_interval_arf(x, ul + i, uh + i, prec);
        arb_poly_evaluate(v, Q, x, prec); arb_abs(v, v);
        arb_set_arf(a, ul + i); arb_set_arf(b, uh + i); arb_sub(t, b, a, prec);
        arb_mul(t, t, v, prec); arb_mul(t, t, C_PHI0, prec);
        arb_get_ubound_arf(arb_midref(x), t, prec); mag_zero(arb_radref(x)); arb_add(res, res, x, prec);
    }
    arb_poly_clear(Q); arb_clear(a); arb_clear(b); arb_clear(x); arb_clear(v); arb_clear(t);
    for (int k = 0; k < 4; k++) arb_clear(I[k]);
    for (int i = 0; i < 3; i++) { arf_clear(lo + i); arf_clear(hi + i); arf_clear(ul + i); arf_clear(uh + i); }
    return fail ? -1 : 0;
}

/* J(c, a) enclosure (upper endpoint is a rigorous upper bound); returns -1 on failure */
static int Jfun(arb_t J, const arb_t c, arb_srcptr a, slong prec)
{
    arb_struct q1[4], q2[4]; for (int k = 0; k < 4; k++) { arb_init(q1 + k); arb_init(q2 + k); }
    arb_t t; arb_init(t);
    arb_mul(t, a + 2, C_RSQ2, prec); arb_sub(q1 + 0, a + 0, t, prec); arb_set(q1 + 2, t);
    arb_mul(t, a + 3, C_RSQ6, prec); arb_set(q1 + 3, t); arb_mul_ui(t, t, 3, prec); arb_sub(q1 + 1, a + 1, t, prec);
    for (int k = 0; k < 4; k++) arb_set(q2 + k, q1 + k);
    arb_sub(q1 + 1, q1 + 1, c, prec); arb_add(q2 + 1, q2 + 1, c, prec);
    arb_t s; arb_init(s); arb_zero(J); int f = 0;
    f |= half_posint(s, q1, +1, +1, prec); arb_add(J, J, s, prec);
    f |= half_posint(s, q2, -1, +1, prec); arb_add(J, J, s, prec);
    f |= half_posint(s, q2, +1, -1, prec); arb_add(J, J, s, prec);
    f |= half_posint(s, q1, -1, -1, prec); arb_add(J, J, s, prec);
    arb_clear(s); arb_clear(t); for (int k = 0; k < 4; k++) { arb_clear(q1 + k); arb_clear(q2 + k); }
    return f ? -1 : 0;
}

/* d(c) = (3 nu / 2) / (sqrt(1 + c^2) + c) */
static void dfun(arb_t d, const arb_t c, slong prec)
{
    arb_t t; arb_init(t); arb_sqr(t, c, prec); arb_add_ui(t, t, 1, prec); arb_sqrt(t, t, prec); arb_add(t, t, c, prec);
    arb_mul_ui(d, C_NU, 3, prec); arb_mul_2exp_si(d, d, -1); arb_div(d, d, t, prec); arb_clear(t);
}
