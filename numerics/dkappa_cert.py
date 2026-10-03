"""Rigorous enclosure of D_kappa (V478 manuscript, Eqs. 49-50) by validated Taylor integration,
and of the two curve lengths printed after Eq. (50).

Reduction (exact).  Both curves are symmetric about the x-axis and both normalised-arclength
parametrisations start at theta = -pi, so u = 1/2 corresponds to theta = 0 on both curves and
D_kappa^2 = 2 int_{1/2}^{1} (kE - kL)^2 du.  Writing u = 1/2 + s_E(theta)/(2 L_E) with
L_E = int_0^pi sigma_E (half-length) and phi(theta) for the limacon angle with the same u,
    phi'(theta) = R sigma_E(theta) / sigma_L(phi),   phi(0) = 0,   R = L_L / L_E,
    D_kappa^2  = (1/L_E) int_0^pi (kappa_E(theta) - kappa_L(phi(theta)))^2 sigma_E(theta) dtheta,
where sigma = sqrt(r^2 + r'^2) and kappa = (r^2 + 2 r'^2 - r r'') / sigma^3 (both numerators are
positive: V478 Eq. (40) and Cor. 3.8, so the absolute value in Eq. (49) can be dropped).

Validation.  On each step [theta_i, theta_i + h] the Taylor coefficients of order < p are
enclosed at the step start; the order-p coefficient is enclosed over the whole step (Lagrange
remainder), using an a-priori enclosure of phi on the step obtained by Picard iteration.
r_E(theta) = sum_k (-1)^k theta^(2k) / (4^k (2k+1)!) is used as a degree-2K polynomial plus a
rigorous tail bound on every Taylor coefficient.  b_E, a_E come from the Si power series with
alternating-tail bounds.  The same code runs on two independent interval backends.

Usage: python3 dkappa_cert.py mp    (mpmath.iv)
       python3 dkappa_cert.py fx    (independent exact-integer fixed point, ia_fixed.py)
"""
import sys, time
from fractions import Fraction as Fr
from math import comb, factorial
from tseries import TS, ts_sqrt, ts_sincos

PRINTED = "0.203783759536049443826081"
ORDER = 30        # Taylor order p
NSTEPS = 56       # steps on [0, pi]
KPOLY = 70        # r_E polynomial: degree 2*KPOLY

# ------------------------------------------------------------------ backends
class MPB:
    name = "mpmath.iv, 70 digits"
    def __init__(self):
        from mpmath import iv
        iv.dps = 70
        self.iv = iv
        self.sin, self.cos, self.sqrt, self.pi = iv.sin, iv.cos, iv.sqrt, iv.pi
    def const(self, x):
        x = Fr(x); return self.iv.mpf(x.numerator) / self.iv.mpf(x.denominator)
    def sym(self, t):  # [-t, t] for a non-negative Fraction t
        u = self.const(t); return self.iv.mpf([-u.b, u.b])
    def hull(self, a, b): return self.iv.mpf([min(a.a, b.a), max(a.b, b.b)])
    def ends(self, x):
        from mpmath import libmp
        return tuple(Fr(*libmp.to_rational(t)) for t in x._mpi_)
    def subset(self, a, b):  # a inside b
        return b.a <= a.a and a.b <= b.b
    def zero_to(self, x):  # [0, x.hi] for x >= 0
        return self.iv.mpf([0, x.b])

class FXB:
    name = "ia_fixed (exact integers, 560-bit)"
    def __init__(self):
        import ia_fixed as F
        self.F = F
        self.sin, self.cos, self.sqrt, self.pi = F.sin, F.cos, F.sqrt, F.PI
    def const(self, x): return self.F.FI.frac(Fr(x))
    def sym(self, t):
        u = self.F.FI.frac(Fr(t)); return self.F.FI(-u.hi, u.hi)
    def hull(self, a, b): return self.F.FI.hull(a, b)
    def ends(self, x): return x.to_fraction_bounds()
    def subset(self, a, b): return b.lo <= a.lo and a.hi <= b.hi
    def zero_to(self, x): return self.F.FI(0, x.hi)

# ------------------------------------------------------------------ constants
def Si(B, x, xmax):
    """Si(x) for an interval 0 < x <= xmax (Fraction bound), power series + alternating tail."""
    s, term, k = B.const(0), x, 0   # term = x^(2k+1)/(2k+1)!
    while True:
        s = s + (term / (2 * k + 1) if k % 2 == 0 else B.const(0) - term / (2 * k + 1))
        k += 1
        term = term * x * x / ((2 * k) * (2 * k + 1))
        if (2 * k + 2) * (2 * k + 3) > xmax * xmax * 4 and k > 60:
            hi = B.ends(term)[1] / (2 * k + 1)
            if hi < Fr(1, 10**90):
                return s + B.sym(hi)

def limacon_coeffs(B):
    pi = B.pi
    s1 = Si(B, pi / 2, Fr(2))
    s3 = Si(B, pi * 3 / 2, Fr(5))
    bE = B.const(2) / pi * s1
    aE = B.const(2) / pi * (s3 - s1)
    return bE, aE

_C = [Fr((-1) ** k, 4**k * factorial(2 * k + 1)) for k in range(KPOLY + 1)]
def _tail(j):
    """Bound on |j-th Taylor coeff of sum_{k>K} c_k x^(2k)| for |x| <= 4 (ratio test <= 1/2, see doc)."""
    k = KPOLY + 1
    return 2 * Fr(comb(2 * k, j) * 4 ** (2 * k - j), 4**k * factorial(2 * k + 1))
_TAILS = {}

def rE_series(B, x0, n):
    X = TS.var(B, x0, n)
    X2 = X * X
    P = TS.const(B, B.const(_C[KPOLY]), n)
    for k in range(KPOLY - 1, -1, -1):
        P = P * X2 + B.const(_C[k])
    out = []
    for j in range(n + 1):
        if j not in _TAILS:
            _TAILS[j] = _tail(j)
        out.append(P.c[j] + B.sym(_TAILS[j]))
    return TS(B, out)

def theta_part(B, x0, n):
    """Series (order n) of sigma_E and kappa_E at expansion point x0 (thin or box)."""
    r = rE_series(B, x0, n + 2)
    r1 = r.deriv()
    r2 = r1.deriv()
    r, r1 = r.trunc(n), r1.trunc(n)
    A = r * r + r1 * r1
    sig = ts_sqrt(A)
    num = r * r + r1 * r1 * 2 - r * r2
    kap = num / (A * sig)
    return sig, kap

def limacon_part(B, phi, bE, aE):
    s, c = ts_sincos(phi)
    A = c * (bE * aE * 2) + (bE * bE + aE * aE)
    sig = ts_sqrt(A)
    num = c * (bE * aE * 3) + (bE * bE + aE * aE * 2)
    kap = num / (A * sig)
    return sig, kap

def phi_series(B, phi0, sigE, R, bE, aE, p):
    """Taylor coefficients 0..p of phi with phi(start)=phi0 (interval), by successive extension."""
    coeffs = [phi0]
    for k in range(p):
        cur = TS(B, coeffs + [B.const(0)] * (p - len(coeffs)))   # orders >= len unknown, not used below
        sL, _ = limacon_part(B, cur, bE, aE)
        f = (sigE.trunc(k) * R) / sL.trunc(k)
        coeffs.append(f.c[k] / (k + 1))
    return TS(B, coeffs)

def quad_step(B, ser_c, ser_box_p, h, p):
    """int_0^h of a function with centre series ser_c (orders < p) and order-p box coefficient."""
    s = B.const(0)
    hk = h
    for k in range(p):
        s = s + ser_c.c[k] * hk / (k + 1)
        hk = hk * h
    return s + ser_box_p * hk / (p + 1)

def run(B):
    t0 = time.time()
    p, N = ORDER, NSTEPS
    pi = B.pi
    bE, aE = limacon_coeffs(B)
    h = pi / N
    grid = [B.const(Fr(i, N)) * pi for i in range(N + 1)]
    # --- half lengths
    LE, LL = B.const(0), B.const(0)
    for i in range(N):
        box = B.hull(grid[i], grid[i + 1])
        sc, _ = theta_part(B, grid[i], p)
        sb, _ = theta_part(B, box, p)
        LE = LE + quad_step(B, sc, sb.c[p], h, p)
        lc, _ = limacon_part(B, TS.var(B, grid[i], p), bE, aE)
        lb, _ = limacon_part(B, TS.var(B, box, p), bE, aE)
        LL = LL + quad_step(B, lc, lb.c[p], h, p)
    R = LL / LE
    # --- validated ODE + integral
    phi = B.const(0)
    I = B.const(0)
    for i in range(N):
        box = B.hull(grid[i], grid[i + 1])
        sE_c, kE_c = theta_part(B, grid[i], p)
        sE_b, kE_b = theta_part(B, box, p)
        # a-priori enclosure of phi on the step (Picard)
        sE_box_val = sE_b.c[0]
        Bphi = phi
        for _ in range(60):
            sl, _ = limacon_part(B, TS.const(B, Bphi, 0), bE, aE)
            fbox = R * sE_box_val / sl.c[0]
            new = phi + B.zero_to(fbox * h)
            lo, hi = B.ends(new)
            infl = (hi - lo) / 16 + Fr(1, 10**60)
            cand = B.hull(B.const(lo - infl), B.const(hi + infl))
            if B.subset(new, Bphi):
                break
            Bphi = cand
        else:
            raise RuntimeError("Picard enclosure failed")
        # Taylor coefficients: centre (orders < p) and box (order p)
        ph_c = phi_series(B, phi, sE_c, R, bE, aE, p)
        ph_b = phi_series(B, Bphi, sE_b, R, bE, aE, p)
        # integrand (kE - kL)^2 sigma_E
        _, kL_c = limacon_part(B, ph_c, bE, aE)
        _, kL_b = limacon_part(B, ph_b, bE, aE)
        g_c = (kE_c - kL_c) * (kE_c - kL_c) * sE_c
        g_b = (kE_b - kL_b) * (kE_b - kL_b) * sE_b
        I = I + quad_step(B, g_c, g_b.c[p], h, p)
        # advance phi
        new_phi = B.const(0)
        hk = B.const(1)
        for k in range(p):
            new_phi = new_phi + ph_c.c[k] * hk
            hk = hk * h
        phi = new_phi + ph_b.c[p] * hk
    D2 = I / LE
    D = B.sqrt(D2)
    lo, hi = B.ends(D)
    plo, phi_ = B.ends(phi)
    pilo, pihi = B.ends(pi)
    d = Fr(PRINTED)
    half = Fr(1, 2 * 10**24)
    print(f"backend: {B.name}; order {p}, {N} steps")
    (le0, le1), (ll0, ll1) = B.ends(LE), B.ends(LL)
    print(f"half-lengths: L_E in [{float(le0):.20f}, {float(le1):.20f}], "
          f"L_L in [{float(ll0):.20f}, {float(ll1):.20f}]")
    okE = Fr("5.5510") <= 2 * le0 and 2 * le1 < Fr("5.5511")
    okL = Fr("5.5243") <= 2 * ll0 and 2 * ll1 < Fr("5.5244")
    print(f"lengths printed after Eq. (50): 2 L_E = 5.5510... certified = {okE}; 2 L_L = 5.5243... certified = {okL}")
    print(f"phi(pi) enclosure contains pi: {plo <= pihi and pilo <= phi_}   width {float(phi_ - plo):.3e}")
    print(f"D_kappa in [{lo}, {hi}]")
    print(f"  ~ [{float(lo):.17f}, {float(hi):.17f}], width {float(hi - lo):.3e}")
    ok = d - half < lo and hi < d + half
    print(f"Eq. (50): printed 24-place value {PRINTED}: certified correctly rounded = {ok}")
    print(f"elapsed {time.time() - t0:.1f}s")

if __name__ == "__main__":
    run(MPB() if sys.argv[1] == "mp" else FXB())
