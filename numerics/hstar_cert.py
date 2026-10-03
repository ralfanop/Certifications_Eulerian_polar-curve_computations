"""Rigorous certificate for h_* (V478 Theorem 3.13, Eq. 70): h_* correctly rounded to 80 decimal places.

Notation (manuscript Sec. 3.10): q = 2/pi, c = (1+q)/2, m = (1-q)/2,
Omega_h = {rho(cos t, sin t): 0 <= rho <= c + h + m cos t},  Q(h) = max_{p in Gamma_E} dist(p, Omega_h).
Proven in the manuscript (proof of Thm 3.13): Q(h) - h is strictly decreasing and vanishes at h_*.
Hence  Q(L) > L  and  Q(U) < U  imply  L < h_* < U.

With d the printed 80-place decimal, L = d - 10^-80/2 and U = d + 10^-80/2 (exact rationals).

(1) Q(L) > L.  Witness point p = gamma_E(theta0) and boundary point z = gamma_L(t0) of Omega_L at
    exact rational parameters.  Omega_L is convex (c + L > 2m), so it lies in the half-plane
    {y : N.(y - z) <= 0}, N the outward normal at z; hence dist(p, Omega_L) >= N.(p - z)/|N|.

(2) Q(U) < U.  By the reflection y -> -y it suffices to treat theta in [0, pi].
    (2a) Outside T = [1.98, 2.22]: the point (c+U+m cos th)(cos th, sin th) lies in Omega_U, so
         dist(p, Omega_U) <= max(0, g(cos th) - U) with g = f - l (f(x) = r_E(arccos x), l the chord).
         g is concave on [-1,1] (manuscript Eqs. 62-64), so g(cos th) <= max(g(cos 1.98), g(cos 2.22))
         for th outside T as soon as g(cos 2.1) exceeds both endpoint values.  We check
         g(cos 1.98), g(cos 2.22) < 2U < ... and g(cos 2.1) > max(g(cos 1.98), g(cos 2.22)).
    (2b) On T: adaptive dyadic panels.  On a panel [a,b] with centre th_c and half-width w we use the
         path t(th) = t_c + s (th - th_c) and F(th) = |gamma_E(th) - gamma_U(t(th))|^2 >= dist^2.
         Taylor:  F(th) <= F(th_c) + |F'(th_c)| w + (1/2) sup_[a,b] |F''| w^2, all in interval
         arithmetic; the panel is accepted when this upper bound is < U^2 (or when the
         order-0 enclosure of F over [a,b] already is).  t_c and s are arbitrary exact
         decimals (any choice gives a valid upper bound); they are chosen numerically.

Usage:  python3 hstar_cert.py certify   (mpmath.iv backend, builds and records the cover)
        python3 hstar_cert.py replay    (independent fixed-point backend ia_fixed.py, replays it)
"""
import json, sys, time
from fractions import Fraction as Fr
from jets import Jet, jsin, jcos

D80 = "0.04929794832571833570703662300396701228024147449936041418804532388531218517828559"
d = Fr(D80)
L = d - Fr(1, 2 * 10**80)
U = d + Fr(1, 2 * 10**80)
TA, TB = Fr(198, 100), Fr(222, 100)

# ---------------------------------------------------------------- backends
class MPBackend:
    name = "mpmath.iv (outward-rounded), 150 significant digits"
    def __init__(self):
        from mpmath import iv, mp
        iv.dps = 150
        self.iv, self.mp = iv, mp
        self.sin, self.cos, self.sqrt = iv.sin, iv.cos, iv.sqrt
        self.pi = iv.pi
    def const(self, x):
        x = Fr(x)
        return self.iv.mpf(x.numerator) / self.iv.mpf(x.denominator)
    def hull(self, a, b):
        return self.iv.mpf([min(a.a, b.a), max(a.b, b.b)])
    def upper(self, x): return mpi_end(x, 1)
    def lower(self, x): return mpi_end(x, 0)
    def absb(self, x): return self.iv.mpf([0, max(abs(x.a), abs(x.b))])

class FXBackend:
    name = "ia_fixed.py (exact integers, 560-bit fixed point, own series for sin/cos/pi)"
    def __init__(self):
        import ia_fixed as F
        self.F = F
        self.sin, self.cos, self.sqrt = F.sin, F.cos, F.sqrt
        self.pi = F.PI
    def const(self, x): return self.F.FI.frac(Fr(x))
    def hull(self, a, b): return self.F.FI.hull(a, b)
    def upper(self, x): return x.to_fraction_bounds()[1]
    def lower(self, x): return x.to_fraction_bounds()[0]
    def absb(self, x): return x.abs()

def mpi_end(x, k):
    """Exact rational value of an endpoint of an mpmath interval (no re-rounding)."""
    from mpmath import libmp
    p, q = libmp.to_rational(x._mpi_[k])
    return Fr(p, q)

# ---------------------------------------------------------------- geometry (shared formulas)
def consts(B):
    q = B.const(2) / B.pi
    c = (B.const(1) + q) / 2
    m = (B.const(1) - q) / 2
    return q, c, m

def rE_jet(th):
    return 2 * jsin(th * Fr(1, 2)) / th

def F_jet(B, th, t, h, cm):
    c, m = cm
    r = rE_jet(th)
    px, py = r * jcos(th), r * jsin(th)
    rl = jcos(t) * m + (c + h)
    zx, zy = rl * jcos(t), rl * jsin(t)
    dx, dy = px - zx, py - zy
    return dx * dx + dy * dy

def thin(B, x):
    return Jet(B, B.const(x), B.const(1), B.const(0))

# ---------------------------------------------------------------- numerics for path choice
def numeric_tc_s(theta_c, h):
    import mpmath as mp
    mp.mp.dps = 90
    q = 2 / mp.pi; c = (1 + q) / 2; m = (1 - q) / 2
    th = mp.mpf(theta_c.numerator) / theta_c.denominator
    hh = mp.mpf(h.numerator) / h.denominator
    def tc_of(th):
        r = 2 * mp.sin(th / 2) / th
        px, py = r * mp.cos(th), r * mp.sin(th)
        def G(t):
            rl, drl = c + hh + m * mp.cos(t), -m * mp.sin(t)
            zx, zy = rl * mp.cos(t), rl * mp.sin(t)
            tx, ty = drl * mp.cos(t) - rl * mp.sin(t), drl * mp.sin(t) + rl * mp.cos(t)
            return (px - zx) * tx + (py - zy) * ty
        return mp.findroot(G, th)
    tc = tc_of(th)
    eps = mp.mpf(10) ** -30
    s = (tc_of(th + eps) - tc_of(th - eps)) / (2 * eps)
    return mp.nstr(tc, 55), mp.nstr(s, 25)

# ---------------------------------------------------------------- checks
def check_lower(B, wit):
    """Q(L) > L via supporting half-plane at an exact boundary point."""
    _, c, m = consts(B)
    th, t = B.const(Fr(wit["theta0"])), B.const(Fr(wit["t0"]))
    Lb = B.const(L)
    r = B.const(2) * B.sin(th / 2) / th
    px, py = r * B.cos(th), r * B.sin(th)
    rl, drl = c + Lb + m * B.cos(t), (B.const(0) - m) * B.sin(t)
    zx, zy = rl * B.cos(t), rl * B.sin(t)
    tx, ty = drl * B.cos(t) - rl * B.sin(t), drl * B.sin(t) + rl * B.cos(t)
    nx, ny = ty, B.const(0) - tx          # outward normal of the counter-clockwise boundary
    lowb = (nx * (px - zx) + ny * (py - zy)) / B.sqrt(nx * nx + ny * ny)
    ok_convex = B.lower(c + Lb - 2 * m) > 0
    return ok_convex and B.lower(lowb) > L, B.lower(lowb) - L

def g_val(B, thx):
    _, c, m = consts(B)
    th = B.const(thx)
    return B.const(2) * B.sin(th / 2) / th - c - m * B.cos(th)

def check_outside(B):
    ga, gb, gm = g_val(B, TA), g_val(B, TB), g_val(B, Fr(21, 10))
    two_u = 2 * U
    ok = (B.upper(ga) < two_u and B.upper(gb) < two_u
          and B.lower(gm) > max(B.upper(ga), B.upper(gb)))
    return ok, (float(B.upper(ga)), float(B.upper(gb)), float(B.lower(gm)), float(two_u))

def panel_bound(B, a, b, tc, s, cm, Ub, order0_first=True):
    thc = (a + b) / 2
    w = (b - a) / 2
    S = B.const(s)
    Tc = B.const(tc)
    # order 0 over the box
    box_th = B.hull(B.const(a), B.const(b))
    box_t = Tc + S * (box_th - B.const(thc))
    Fbox = F_jet(B, Jet(B, box_th, B.const(1), B.const(0)), Jet(B, box_t, S, B.const(0)), Ub, cm)
    U2 = U * U
    if order0_first and B.upper(Fbox.v) < U2:
        return True, "o0", B.upper(Fbox.v)
    Fc = F_jet(B, thin(B, thc), Jet(B, Tc, S, B.const(0)), Ub, cm)
    W = B.const(w)
    bound = Fc.v + B.absb(Fc.d) * W + B.absb(Fbox.dd) * (W * W) / 2
    return B.upper(bound) < U2, "t2", B.upper(bound)

def certify():
    B = MPBackend()
    t0 = time.time()
    import mpmath as mp
    # witness for Q(L) > L (numeric critical configuration at h = L)
    mp.mp.dps = 140
    q = 2 / mp.pi; c = (1 + q) / 2; m = (1 - q) / 2
    hL = mp.mpf(L.numerator) / L.denominator
    rE = lambda t: 2 * mp.sin(t / 2) / t
    drE = lambda t: mp.cos(t / 2) / t - 2 * mp.sin(t / 2) / t**2
    def sysF(th, t):
        px, py = rE(th) * mp.cos(th), rE(th) * mp.sin(th)
        ex, ey = drE(th) * mp.cos(th) - rE(th) * mp.sin(th), drE(th) * mp.sin(th) + rE(th) * mp.cos(th)
        rl, drl = c + hL + m * mp.cos(t), -m * mp.sin(t)
        zx, zy = rl * mp.cos(t), rl * mp.sin(t)
        tx, ty = drl * mp.cos(t) - rl * mp.sin(t), drl * mp.sin(t) + rl * mp.cos(t)
        return [(px - zx) * tx + (py - zy) * ty, (px - zx) * ex + (py - zy) * ey]
    th0, tt0 = mp.findroot(sysF, (mp.mpf("2.1074"), mp.mpf("2.0956")))
    wit = {"theta0": mp.nstr(th0, 120), "t0": mp.nstr(tt0, 120)}
    okL, gapL = check_lower(B, wit)
    print(f"[1] Q(L) > L : {okL}   certified gap dist - L > {float(gapL):.4e}")
    okO, vals = check_outside(B)
    print(f"[2a] concavity outside [1.98,2.22]: {okO}  g(cos1.98)<= {vals[0]:.6f}, g(cos2.22)<= {vals[1]:.6f}, g(cos2.1)>= {vals[2]:.6f}, 2U={vals[3]:.6f}")
    # adaptive cover
    _, cc, mm = consts(B)
    Ub = B.const(U)
    panels, stack, maxdepth = [], [(0, 0)], 0
    while stack:
        dep, idx = stack.pop()
        a = TA + (TB - TA) * Fr(idx, 2**dep)
        b = TA + (TB - TA) * Fr(idx + 1, 2**dep)
        tc, s = numeric_tc_s((a + b) / 2, U)
        ok, kind, val = panel_bound(B, a, b, Fr(tc), Fr(s), (cc, mm), Ub)
        if ok:
            panels.append({"depth": dep, "index": idx, "tc": tc, "s": s, "kind": kind})
            maxdepth = max(maxdepth, dep)
        else:
            if dep > 200:
                raise RuntimeError("cover failed")
            stack += [(dep + 1, 2 * idx + 1), (dep + 1, 2 * idx)]
    # coverage check (exact): panels tile [TA, TB]
    ivs = sorted((Fr(p["index"], 2**p["depth"]), Fr(p["index"] + 1, 2**p["depth"])) for p in panels)
    tiled = ivs[0][0] == 0 and ivs[-1][1] == 1 and all(x[1] == y[0] for x, y in zip(ivs, ivs[1:]))
    print(f"[2b] cover of [1.98,2.22]: {len(panels)} panels, max depth {maxdepth}, exact tiling: {tiled}, "
          f"order-0 panels {sum(p['kind']=='o0' for p in panels)}, Taylor panels {sum(p['kind']=='t2' for p in panels)}")
    allok = okL and okO and tiled
    print("RESULT (mpmath.iv):", "L < h_* < U certified; the 80-place decimal of h_* is correctly rounded" if allok else "FAILED")
    json.dump({"D80": D80, "L": str(L), "U": str(U), "interval": [str(TA), str(TB)], "witness_lower": wit,
               "panels": panels, "backend": B.name, "seconds": time.time() - t0},
              open("hstar_certificate.json", "w"), indent=0)
    print(f"elapsed {time.time() - t0:.1f}s")

def replay():
    B = FXBackend()
    t0 = time.time()
    cert = json.load(open("hstar_certificate.json"))
    assert cert["D80"] == D80 and Fr(cert["L"]) == L and Fr(cert["U"]) == U
    okL, gapL = check_lower(B, cert["witness_lower"])
    print(f"[1] Q(L) > L : {okL}   gap > {float(gapL):.4e}")
    okO, vals = check_outside(B)
    print(f"[2a] concavity outside [1.98,2.22]: {okO}")
    _, cc, mm = consts(B)
    Ub = B.const(U)
    bad = 0
    for p in cert["panels"]:
        a = TA + (TB - TA) * Fr(p["index"], 2**p["depth"])
        b = TA + (TB - TA) * Fr(p["index"] + 1, 2**p["depth"])
        ok, _, _ = panel_bound(B, a, b, Fr(p["tc"]), Fr(p["s"]), (cc, mm), Ub, order0_first=(p["kind"] == "o0"))
        if not ok:
            ok, _, _ = panel_bound(B, a, b, Fr(p["tc"]), Fr(p["s"]), (cc, mm), Ub, order0_first=False)
        bad += (not ok)
    ivs = sorted((Fr(p["index"], 2**p["depth"]), Fr(p["index"] + 1, 2**p["depth"])) for p in cert["panels"])
    tiled = ivs[0][0] == 0 and ivs[-1][1] == 1 and all(x[1] == y[0] for x, y in zip(ivs, ivs[1:]))
    print(f"[2b] {len(cert['panels'])} panels replayed, failures: {bad}, exact tiling: {tiled}")
    allok = okL and okO and tiled and bad == 0
    print("RESULT (independent fixed-point replay):", "L < h_* < U certified" if allok else "FAILED")
    print(f"elapsed {time.time() - t0:.1f}s")

if __name__ == "__main__":
    {"certify": certify, "replay": replay}[sys.argv[1]]()
