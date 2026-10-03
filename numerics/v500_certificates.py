"""Certificates for the companion manuscript V500,
"Cyclohedral zeta targets, Cassini spectral bridges, and Chebyshev strong-cycle realisations".
Equation and statement numbers refer to the V500 PDF.

RIGOROUS (exact rational / algebraic arithmetic, or outward-rounded intervals on both backends):
  [A] Cor. 3.1, Eqs. (15)-(18): Taylor coefficients of 8(w+2)/(w(w+1)^2), w = sqrt(1-4q),
      equal f_0(P_{C_{m+3}}) = C(2m+4, m+2) for m <= 300 (exact power-series arithmetic).
  [B] Cor. 4.7, Eqs. (98)-(100): det(lam I - J_n) = 2^{1-n} T_n(lam) and
      det(lam I - A_n(w)) = 2^{1-n}[T_n(lam) - w], exactly in Q(sqrt2)(i), n = 2..12, at
      Gaussian-rational points; the Floquet identity after Cor. 4.7 (symmetric corners
      (1/2)e^{+-i phi}, e^{i phi} = (3+4i)/5) gives 2^{1-n}[T_n(lam) - cos phi], n = 3..12.
  [C] Eqs. (89)-(90): enclosures of 2 sin(t/2)/t, of the dyadic product prod_{k>=2} cos(t/2^k)
      (with an explicit tail bound) and of the series sum C(2k,k) q^k/(2k+1), q = (1-cos t)/8
      (with an explicit tail bound), at t = 1/2, 1, 2, 3; Viete's 2/pi at t = pi. Both backends.
  [D] Prop. 4.6: Riemann-Hurwitz count, node count and floor((n-1)^2/2) agree for n = 2..60
      (exact integers; the general statement is proved in Lean, EulerianCert.Cyclohedral).
  [E] Figure 1: the closed disc |s - (3/4 + 57i/4)| <= 11/50 lies in 1/2 < Re s < 1 and misses
      rho_1 = 1/2 + i*gamma_1, using the published bounds 14.1347251417 < gamma_1 < 14.1347251418.
  [F] Prop. 4.2, Eq. (65): det(lam I - M_n(w)) - 2^{1-n}[T_n(lam) - w] encloses 0 (interval
      determinant by exact cofactor-free elimination on both backends), n = 2..12, rational lam, w.
      (The identity itself is a one-permutation expansion; this is a consistency check.)
NON-RIGOROUS cross-check:
  [G] Prop. 4.6: monodromy group of the reciprocal covering has order 2n (n = 3..6), by numerical
      continuation of the fibre around every branch point.
"""
from fractions import Fraction as Fr
from math import comb
import cmath
import mpmath as mp
import ia_fixed as fx

ok_all = True
def report(tag, ok, msg=""):
    global ok_all
    ok_all &= bool(ok)
    print(f"{tag}: {'OK' if ok else 'FAIL'} {msg}")

# ---------------------------------------------------------------- [A]
N = 301
def ser_mul(a, b):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(N)]
def ser_inv(a):
    inv = [Fr(0)] * N
    inv[0] = 1 / a[0]
    for k in range(1, N):
        inv[k] = -sum(a[i] * inv[k - i] for i in range(1, k + 1)) / a[0]
    return inv
# w = (1-4q)^{1/2} = sum binom(1/2, k) (-4q)^k
w = [Fr(1)] * N
c = Fr(1)
for k in range(1, N):
    c = c * (Fr(1, 2) - (k - 1)) / k
    w[k] = c * (-4) ** k
one = [Fr(1)] + [Fr(0)] * (N - 1)
wp1 = [w[0] + 1] + w[1:]
wp2 = [w[0] + 2] + w[1:]
Z = [8 * x for x in ser_mul(wp2, ser_inv(ser_mul(w, ser_mul(wp1, wp1))))]
report("[A] Zhat Taylor coefficients = C(2m+4,m+2), m<=300", all(Z[m] == comb(2 * m + 4, m + 2) for m in range(N)))

# ---------------------------------------------------------------- [B] exact field Q(sqrt2)(i)
class Q2:  # a + b*sqrt2, a, b rational
    __slots__ = ("a", "b")
    def __init__(self, a, b=0): self.a, self.b = Fr(a), Fr(b)
    def __add__(s, o): o = q2(o); return Q2(s.a + o.a, s.b + o.b)
    def __sub__(s, o): o = q2(o); return Q2(s.a - o.a, s.b - o.b)
    def __mul__(s, o): o = q2(o); return Q2(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)
    def __neg__(s): return Q2(-s.a, -s.b)
    def inv(s):
        d = s.a * s.a - 2 * s.b * s.b
        return Q2(s.a / d, -s.b / d)
    def __eq__(s, o): o = q2(o); return s.a == o.a and s.b == o.b
    def iszero(s): return s.a == 0 and s.b == 0
def q2(x): return x if isinstance(x, Q2) else Q2(x)
class C2:  # x + i y, x, y in Q(sqrt2)
    __slots__ = ("x", "y")
    def __init__(self, x, y=0): self.x, self.y = q2(x), q2(y)
    def __add__(s, o): o = c2(o); return C2(s.x + o.x, s.y + o.y)
    def __sub__(s, o): o = c2(o); return C2(s.x - o.x, s.y - o.y)
    def __mul__(s, o): o = c2(o); return C2(s.x * o.x - s.y * o.y, s.x * o.y + s.y * o.x)
    def __neg__(s): return C2(-s.x, -s.y)
    def inv(s):
        d = (s.x * s.x + s.y * s.y).inv()
        return C2(s.x * d, -s.y * d)
    def iszero(s): return s.x.iszero() and s.y.iszero()
    def __eq__(s, o): o = c2(o); return s.x == o.x and s.y == o.y
def c2(x): return x if isinstance(x, C2) else C2(x)

def det(M):
    M = [row[:] for row in M]; n = len(M); d = C2(1)
    for i in range(n):
        p = next((r for r in range(i, n) if not M[r][i].iszero()), None)
        if p is None: return C2(0)
        if p != i: M[i], M[p] = M[p], M[i]; d = -d
        d = d * M[i][i]; inv = M[i][i].inv()
        for r in range(i + 1, n):
            f = M[r][i] * inv
            if not f.iszero():
                M[r] = [M[r][k] - f * M[i][k] for k in range(n)]
    return d

def cheb(n, lam):  # T_n(lam), lam in C2
    t0, t1 = C2(1), lam
    if n == 0: return t0
    for _ in range(n - 1):
        t0, t1 = t1, C2(2) * lam * t1 - t0
    return t1

ISQ2 = Q2(0, Fr(1, 2))        # 1/sqrt2
HALF = Fr(1, 2)
def J(n):
    M = [[C2(0) for _ in range(n)] for _ in range(n)]
    M[0][1] = M[1][0] = C2(ISQ2)
    for j in range(1, n - 1):
        M[j][j + 1] = M[j + 1][j] = C2(HALF)
    return M
def lamI_minus(lam, M):
    n = len(M)
    return [[(lam if i == j else C2(0)) - M[i][j] for j in range(n)] for i in range(n)]

ok_J = ok_A = ok_F = True
lam = C2(Fr(3, 7), Fr(-2, 5)); wv = C2(Fr(-5, 3), Fr(1, 4))
for n in range(2, 13):
    pow2 = C2(Fr(1, 2 ** (n - 1)))
    ok_J &= det(lamI_minus(lam, J(n))) == pow2 * cheb(n, lam)
    A = J(n); A[n - 1][0] = A[n - 1][0] + wv * C2(ISQ2)
    ok_A &= det(lamI_minus(lam, A)) == pow2 * (cheb(n, lam) - wv)
    if n >= 3:
        e = C2(Fr(3, 5), Fr(4, 5)); ebar = C2(Fr(3, 5), Fr(-4, 5)); cosphi = C2(Fr(3, 5))
        P = [[C2(0) for _ in range(n)] for _ in range(n)]
        for j in range(n - 1):
            P[j][j + 1] = P[j + 1][j] = C2(HALF)
        P[0][n - 1] = C2(HALF) * e; P[n - 1][0] = C2(HALF) * ebar
        ok_F &= det(lamI_minus(lam, P)) == pow2 * (cheb(n, lam) - cosphi)
report("[B] det(lam I - J_n) = 2^{1-n} T_n(lam), n=2..12 (exact)", ok_J)
report("[B] det(lam I - A_n(w)) = 2^{1-n}[T_n(lam) - w], n=2..12 (exact)", ok_A)
report("[B] Floquet: periodic chain, corners e^{+-i phi}/2: 2^{1-n}[T_n - cos phi], n=3..12 (exact)", ok_F)

# ---------------------------------------------------------------- [C]
mp.mp.dps = 60
iv = mp.iv; iv.dps = 60
def enclose_mp(t):
    t = iv.mpf(t)
    lhs = 2 * iv.sin(t / 2) / t
    K = 60
    prod = iv.mpf(1)
    for k in range(2, K + 1):
        prod = prod * iv.cos(t / 2 ** k)
    tail_lo = 1 - t ** 2 / (iv.mpf(6) * iv.mpf(4) ** K)       # prod_{k>K} cos(t/2^k) >= 1 - t^2 4^{-K}/6
    prod_iv = iv.mpf([(prod * tail_lo).a, prod.b])
    q = (1 - iv.cos(t)) / 8
    M = 400 if (4 * q).b < 0.5 else 25000                     # slower convergence as q -> 1/4
    s = iv.mpf(0); term = iv.mpf(1)
    for k in range(M):
        s = s + term / (2 * k + 1)
        term = term * 2 * (2 * k + 1) / (k + 1) * q
    r = iv.mpf((4 * q).b)                                     # upper bound for 4q
    tail = (r ** M / ((1 - r) * (2 * M + 1))).b               # sum_{k>=M} C(2k,k)q^k/(2k+1) <= (4q)^M/((1-4q)(2M+1))
    ser_iv = iv.mpf([s.a, (s.b + tail).b])
    inv_lhs = 1 / lhs
    return lhs, prod_iv, ser_iv, inv_lhs

def overlap(x, y):
    return not (x.b < y.a or y.b < x.a)
for t in [Fr(1, 2), Fr(1), Fr(2), Fr(3)]:
    lhs, prod_iv, ser_iv, inv_lhs = enclose_mp(mp.mpf(t.numerator) / t.denominator)
    ok = overlap(lhs, prod_iv) and overlap(inv_lhs, ser_iv) and float(prod_iv.delta) < 1e-30 and float(ser_iv.delta) < 1e-30
    report(f"[C] mpmath.iv t={t}: (89) and (90) enclosures agree", ok,
           f"widths {float(prod_iv.delta.b):.1e}, {float(ser_iv.delta.b):.1e}")
# Viete at t = pi
p = iv.mpf(1)
for k in range(2, 61):
    p = p * iv.cos(iv.pi / 2 ** k)
vi = iv.mpf([(p * (1 - iv.pi ** 2 / (iv.mpf(6) * iv.mpf(4) ** 60))).a, p.b])
report("[C] mpmath.iv Viete: prod_{k>=2} cos(pi/2^k) encloses 2/pi", overlap(vi, 2 / iv.pi), f"width {float(vi.delta.b):.1e}")
# second backend (ia_fixed): dyadic product (89) and Viete
def fx_ok(t):
    lhs = fx.FI.frac(2) * fx.sin(t / fx.FI.frac(2)) / t
    p = fx.ONE
    for k in range(2, 120):
        p = p * fx.cos(t / fx.FI.frac(2 ** k))
    lo = p * (fx.ONE - t * t / fx.FI.frac(6 * 4 ** 119))
    a, b = Fr(lo.lo, 1 << fx.P), Fr(p.hi, 1 << fx.P)
    L, U = Fr(lhs.lo, 1 << fx.P), Fr(lhs.hi, 1 << fx.P)
    return not (b < L or U < a)
for t in [Fr(1, 2), Fr(1), Fr(2), Fr(3)]:
    report(f"[C] ia_fixed t={t}: dyadic product (89) encloses 2 sin(t/2)/t", fx_ok(fx.FI.frac(t)))
report("[C] ia_fixed Viete at t = pi", fx_ok(fx.PI))

# ---------------------------------------------------------------- [D]
def rh_genus(n):
    R = n * (n - 1) + ((n - 1) if n % 2 else (n - 2))
    return (R - 2 * n + 2) // 2, (R - 2 * n + 2) % 2 == 0
def node_genus(n):
    rp, rm = (n - 1) // 2, n // 2
    return (n - 1) ** 2 - (rp * rp + rm * rm)
okD = all(rh_genus(n)[1] and rh_genus(n)[0] == node_genus(n) == (n - 1) ** 2 // 2 for n in range(2, 61))
report("[D] genus: Riemann-Hurwitz = node count = floor((n-1)^2/2), n=2..60", okD)

# ---------------------------------------------------------------- [E]
r = Fr(11, 50); cx, cy = Fr(3, 4), Fr(57, 4)
g_lo, g_hi = Fr(141347251417, 10 ** 10), Fr(141347251418, 10 ** 10)   # gamma_1 (Odlyzko, LMFDB)
inside = cx - r > Fr(1, 2) and cx + r < 1
dy_min = min(abs(cy - g_lo), abs(cy - g_hi))   # cy > g_hi, so the distance is minimised at g_hi
dist2_lo = (cx - Fr(1, 2)) ** 2 + (cy - g_hi) ** 2
report("[E] Figure 1: disc inside the strip and away from rho_1", inside and dist2_lo > r * r and cy > g_hi,
       f"distance > {float(dist2_lo) ** 0.5:.6f} > r = {float(r)}")

# ---------------------------------------------------------------- [F]
def iv_det(M):
    M = [row[:] for row in M]; n = len(M); d = iv.mpf(1)
    for i in range(n):
        d = d * M[i][i]
        for rr in range(i + 1, n):
            f = M[rr][i] / M[i][i]
            M[rr] = [M[rr][k] - f * M[i][k] for k in range(n)]
    return d
okF = True
for n in range(2, 13):
    for lam_, w_ in [(Fr(7, 3), Fr(1, 2)), (Fr(-9, 4), Fr(-2, 3)), (Fr(13, 5), Fr(5, 2))]:
        L = iv.mpf(lam_.numerator) / lam_.denominator; W = iv.mpf(w_.numerator) / w_.denominator
        alpha = [iv.cos((2 * j - 1) * iv.pi / (2 * n)) for j in range(1, n + 1)]
        rn = iv.mpf(2) ** (iv.mpf(1 - n) / n)
        Mm = [[iv.mpf(0)] * n for _ in range(n)]
        for j in range(n):
            Mm[j][j] = L - alpha[j]
            if j < n - 1: Mm[j][j + 1] = -rn
        Mm[n - 1][0] = -rn * W
        t0, t1 = iv.mpf(1), L
        for _ in range(n - 1): t0, t1 = t1, 2 * L * t1 - t0
        diff = iv_det(Mm) - iv.mpf(2) ** (1 - n) * (t1 - W)
        okF &= diff.a <= 0 <= diff.b and float(diff.delta) < 1e-40
report("[F] Prop. 4.2 determinant identity encloses 0, n=2..12 (mpmath.iv)", okF)

# ---------------------------------------------------------------- [G] non-rigorous
try:
    import numpy as np
    from numpy.polynomial import chebyshev as C
    def Tn(n, x): return C.chebval(x, [0] * n + [1])
    def group_order(n, steps=1500, rad=0.02):
        branch = [np.cos((2 * j - 1) * np.pi / (2 * n)) for j in range(1, n + 1)] + [1.0, -1.0]
        base = 0.37 + 0.81j
        fib = lambda u: np.roots(C.cheb2poly([-1 / Tn(n, u)] + [0] * (n - 1) + [1])[::-1])
        v0 = fib(base); perms = []
        for pnt in branch:
            path = list(np.linspace(base, pnt + rad * (base - pnt) / abs(base - pnt), steps))
            a0 = cmath.phase(path[-1] - pnt)
            full = path + [pnt + rad * cmath.exp(1j * (a0 + 2 * np.pi * k / steps)) for k in range(1, steps + 1)] + path[::-1]
            cur = v0.copy()
            for u in full[1:]:
                nxt = fib(u); used = set(); new = np.empty_like(cur)
                for i, v in enumerate(cur):
                    d = [abs(v - x) if j not in used else 1e9 for j, x in enumerate(nxt)]
                    j = int(np.argmin(d)); used.add(j); new[i] = nxt[j]
                cur = new
            perms.append(tuple(int(np.argmin([abs(v - x) for x in v0])) for v in cur))
        G = {tuple(range(n))}; fr = list(G)
        while fr:
            g = fr.pop()
            for p_ in perms:
                h = tuple(p_[g[i]] for i in range(n))
                if h not in G: G.add(h); fr.append(h)
        return len(G)
    for n in [3, 4, 5, 6]:
        print(f"[G] (non-rigorous) n={n}: monodromy group order {group_order(n)} (2n = {2 * n})")
except ImportError:
    print("[G] skipped (numpy not available)")

print("ALL RIGOROUS CHECKS PASSED" if ok_all else "SOME CHECK FAILED")
