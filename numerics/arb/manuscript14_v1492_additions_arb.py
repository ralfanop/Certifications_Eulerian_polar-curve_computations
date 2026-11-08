#!/usr/bin/env python3
"""Manuscript 14, version 14.92 of 8 November 2026: certificates of the additions.

Exact integer and rational arithmetic and Arb balls at 2000 bits (python-flint 0.9.0) for the
statements added to version 14.92 that carry a computed value:

  (A) Section 2.1: the discriminant of the Parry trinomial F_n(t) = t^n - t^(n-1) - 1 in the
      normalisation Delta(f) = R(f, f')/a_n of Gelfand-Kapranov-Zelevinsky (Ch. 12, Eq. (1.29),
      p. 404) is (-1)^(n-1) [n^n + (n-1)^(n-1)], nonzero, so all n complex roots are simple.
      Checked by the Sylvester determinant laid out as in GKZ (1.30), coefficients from the
      constant term on, for n = 2..40; by the trinomial formula GKZ (1.38) at a = b = -1, c = 1,
      m = n - 1 for n = 2..300; the normalisation against GKZ (1.33)-(1.35) on random polynomials.
  (B) After the proof of Proposition 8.7: GKZ (1.35) with a_1 = a_3 = 0 equals
      16 a_0 a_4 (4 a_0 a_4 - a_2^2)^2; the discriminant of Bender's P_PT(y) = y^4 + (g^2 - 2) y^2
      + 1 - g^2 [here gamma^2, coupling^2] is 16(1 - g^2)[4(1 - g^2) - (2 - gamma^2)^2]^2; it equals
      s^12/128 > 0 on the family (144)-(145); it vanishes where two frequencies coalesce or one
      frequency vanishes; the discriminant of (139), 32x^4 - 16x^2 + 1, is 2^23.
  (C) After the proof of Proposition 9.5: for the electron, x = mu_B |B|/(k_B T) = a requires
      |B|/T = a k_B/mu_B ~ 0.526 T/K, 2 T at T ~ 3.80 K, population ratio e^(2a) = e^(1/sqrt2)
      ~ 2.028; Exercise 11.8 of Solymar, Walsh and Syms (ratio 2 at 2 T) gives T ~ 3.88 K.
      The rounding is checked with mu_B = 9.274e-24 J/T (the value of Section 4.5) and with the
      CODATA 2018 value 9.2740100783e-24 J/T, and k_B = 1.380649e-23 J/K (exact in the SI).
  (D) After the proof of Proposition 8.6: for a lossless line of loops with self-impedance
      j w L + 1/(j w C) and mutual inductance M, the eigenvalue Z_0 + 2 j w M c of the impedance
      matrix vanishes exactly when f_MI^2/f^2 = 1 + kappa c with kappa = 2M/L and
      f_MI^2 = 1/(4 pi^2 L C); for seven loops the extreme values 2 cos(pi/8), 2 cos(7 pi/8) are
      +-mu_hex.
  (E) Section 9: the matrix U = -i sigma_2 of Lemma 9.2 is the quaternion unit e_2 of the
      representation (12.82) of Pandey, Kumar and Puri, with e_1 = -i sigma_1, e_3 = -i sigma_3,
      e_k^2 = -I and e_1 e_2 = e_3; the Hopf projection (2 conj(z1) z2, |z1|^2 - |z2|^2) of
      Rudolph-Schmidt II, Remark 1.1.21(1), equals psi^dagger sigma psi of (151), and the chart
      (omega_1 + i omega_2)/(1 + omega_3) returns z2/z1 (exact Gaussian-rational arithmetic).
"""
from fractions import Fraction as Q
import random
import sys
import flint
from flint import arb, ctx

PREC = 2000
ctx.prec = PREC
failures = []
count = 0


def check(desc, cond):
    global count
    ok = bool(cond)
    count += 1
    print(f"{'PASS' if ok else 'FAIL'} {count:03d}: {desc}")
    if not ok:
        failures.append(desc)


def qball(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


def rounds_to(x, printed, half_ulp):
    """True when the ball x lies strictly inside (printed - half_ulp, printed + half_ulp)."""
    lo = qball(Q(printed) - Q(half_ulp))
    hi = qball(Q(printed) + Q(half_ulp))
    return bool(x > lo) and bool(x < hi)


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")


# ------------------------------------------------------------- exact linear algebra
def det_exact(M):
    """Determinant of a square matrix of Fractions by Gaussian elimination (exact)."""
    M = [[Q(v) for v in row] for row in M]
    n = len(M)
    d = Q(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None:
            return Q(0)
        if p != i:
            M[i], M[p] = M[p], M[i]
            d = -d
        d *= M[i][i]
        inv = 1 / M[i][i]
        for r in range(i + 1, n):
            if M[r][i] != 0:
                f = M[r][i] * inv
                Mr, Mi = M[r], M[i]
                for c in range(i, n):
                    Mr[c] -= f * Mi[c]
    return d


def sylvester_low(f, g):
    """GKZ layout (1.12)/(1.30): coefficient lists from the constant term on.
    f of degree m (len m+1), g of degree n (len n+1); n rows of f, then m rows of g."""
    m, n = len(f) - 1, len(g) - 1
    N = m + n
    rows = []
    for i in range(n):
        rows.append([0] * i + list(f) + [0] * (N - m - 1 - i))
    for i in range(m):
        rows.append([0] * i + list(g) + [0] * (N - n - 1 - i))
    return rows


def disc_gkz(f):
    """Delta(f) = R(f, f')/a_n with the GKZ layout; f from the constant term on."""
    n = len(f) - 1
    fp = [k * f[k] for k in range(1, n + 1)]
    return det_exact(sylvester_low(f, fp)) / Q(f[-1])


def parry(n):
    """F_n(t) = t^n - t^(n-1) - 1, coefficients from the constant term on."""
    c = [0] * (n + 1)
    c[0], c[n - 1], c[n] = -1, -1, 1
    return c


def closed_form(n):
    return (-1) ** (n - 1) * (n ** n + (n - 1) ** (n - 1))


def gkz_trinomial(a, b, c, m, n):
    """GKZ (1.38): Delta(a + b x^m + c x^n) for 0 < m < n coprime."""
    return (n ** n * a ** (n - 1) * c ** (n - 1)
            + (-1) ** (n - 1) * m ** m * (n - m) ** (n - m) * a ** (m - 1) * b ** n * Q(c) ** (n - m - 1))


def gkz_quartic(a0, a1, a2, a3, a4):
    """GKZ (1.35), transcribed term by term from p. 405."""
    return (256 * a0**3 * a4**3 - 27 * a0**2 * a3**4 - 27 * a1**4 * a4**2 + 16 * a0 * a2**4 * a4
            - 4 * a0 * a2**3 * a3**2 - 4 * a1**2 * a2**3 * a4 - 4 * a1**3 * a3**3 + a1**2 * a2**2 * a3**2
            - 192 * a0**2 * a1 * a3 * a4**2 - 128 * a0**2 * a2**2 * a4**2 + 144 * a0**2 * a2 * a3**2 * a4
            + 144 * a0 * a1**2 * a2 * a4**2 - 6 * a0 * a1**2 * a3**2 * a4 - 80 * a0 * a1 * a2**2 * a3 * a4
            + 18 * a0 * a1 * a2 * a3**3 + 18 * a1**3 * a2 * a3 * a4)


# ---------------------------------------------------------------- (A) Section 2.1
random.seed(20261108)


def rq():
    return Q(random.randint(-9, 9), random.randint(1, 5))


ok2 = ok3 = ok4 = True
for _ in range(40):
    a0, a1, a2 = rq(), rq(), rq()
    if a2 != 0:
        ok2 = ok2 and disc_gkz([a0, a1, a2]) == 4 * a0 * a2 - a1 ** 2
    a3 = rq()
    if a3 != 0:
        ok3 = ok3 and disc_gkz([a0, a1, a2, a3]) == (27 * a0**2 * a3**2 + 4 * a0 * a2**3 + 4 * a1**3 * a3
                                                       - a1**2 * a2**2 - 18 * a0 * a1 * a2 * a3)
    a4 = rq()
    if a4 != 0:
        ok4 = ok4 and disc_gkz([a0, a1, a2, a3, a4]) == gkz_quartic(a0, a1, a2, a3, a4)
check("(A) the GKZ layout R(f, f')/a_n reproduces (1.33) for 40 random rational quadratics", ok2)
check("(A) the GKZ layout R(f, f')/a_n reproduces (1.34) for 40 random rational cubics", ok3)
check("(A) the GKZ layout R(f, f')/a_n reproduces (1.35), as transcribed, for 40 random rational quartics", ok4)

ok = True
vals = {}
for n in range(2, 41):
    d = disc_gkz(parry(n))
    vals[n] = d
    ok = ok and d == closed_form(n) and d != 0
check("(A) Sylvester determinant: Delta(F_n) = (-1)^(n-1)[n^n + (n-1)^(n-1)] != 0 for n = 2..40", ok)
check("(A) the values 5 (up to sign), 31, 283, 3381, 49781 for n = 2..6",
      [abs(vals[n]) for n in range(2, 7)] == [5, 31, 283, 3381, 49781])
check("(A) GKZ (1.38) at a = b = -1, c = 1, m = n - 1 equals (-1)^(n-1)[n^n + (n-1)^(n-1)] for n = 2..300",
      all(gkz_trinomial(-1, -1, 1, n - 1, n) == closed_form(n) for n in range(2, 301)))
check("(A) n - 1 and n are coprime and n^n + (n-1)^(n-1) > 0 for n = 2..300",
      all(__import__('math').gcd(n - 1, n) == 1 and n ** n + (n - 1) ** (n - 1) > 0 for n in range(2, 301)))
check("(A) n = 31, 32: Delta(F_31) = 31^31 + 30^30 and Delta(F_32) = -(32^32 + 31^31)",
      vals[31] == 31 ** 31 + 30 ** 30 and vals[32] == -(32 ** 32 + 31 ** 31))

# ---------------------------------------------------------------- (B) Proposition 8.7
ok = True
for _ in range(60):
    a0, a2, a4 = rq(), rq(), rq()
    ok = ok and gkz_quartic(a0, 0, a2, 0, a4) == 16 * a0 * a4 * (4 * a0 * a4 - a2 ** 2) ** 2
check("(B) (1.35) with a1 = a3 = 0 equals 16 a0 a4 (4 a0 a4 - a2^2)^2 (60 random rational triples)", ok)

G2 = [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(3, 2), Q(7, 4), Q(199, 100)]
C2 = [Q(0), Q(1, 3), Q(1, 2), Q(3, 4), Q(9, 10), Q(1), Q(5, 4)]
ok = True
for gam2 in G2:
    for g2 in C2:
        P = [1 - g2, 0, gam2 - 2, 0, 1]                  # y^4 + (gamma^2 - 2) y^2 + 1 - g^2
        ok = ok and disc_gkz(P) == 16 * (1 - g2) * (4 * (1 - g2) - (2 - gam2) ** 2) ** 2
check("(B) Delta(P_PT) = 16(1 - g^2)[4(1 - g^2) - (2 - gamma^2)^2]^2 (exact Sylvester, 49 rational pairs)", ok)

ok = True
for gam2 in G2:
    s2_ = 4 - 2 * gam2
    g2 = 1 - (2 - gam2) ** 2 / 8
    d = disc_gkz([1 - g2, 0, gam2 - 2, 0, 1])
    ok = ok and d == s2_ ** 6 / 128 and d > 0
check("(B) on (144)-(145): Delta(P_PT) = s^12/128 > 0 for gamma^2 = 0, 1/4, 1/2, 1, 3/2, 7/4, 1.99", ok)
check("(B) at gamma = 0: Delta(P_PT) = 32 (s^2 = 4)", disc_gkz([Q(1, 2), 0, -2, 0, 1]) == 32 and Q(4) ** 6 / 128 == 32)

# coalescence: (2 - gamma^2)^2 = 4(1 - g^2) makes P_PT a square in y^2
ok = True
for gam2 in G2:
    g2 = 1 - (2 - gam2) ** 2 / 4
    P = [1 - g2, 0, gam2 - 2, 0, 1]
    r = (2 - gam2) / 2
    sq = [r * r, 0, -2 * r, 0, 1]                       # (y^2 - r)^2
    ok = ok and P == sq and disc_gkz(P) == 0
check("(B) where (2 - gamma^2)^2 = 4(1 - g^2): P_PT = (y^2 - (2 - gamma^2)/2)^2, two frequencies coalesce, Delta = 0", ok)
ok = True
for gam2 in G2:
    P = [0, 0, gam2 - 2, 0, 1]                          # g^2 = 1
    ok = ok and disc_gkz(P) == 0 and P[0] == 0 and P[1] == 0
check("(B) at g^2 = 1: y = 0 is a double root (one frequency vanishes), Delta = 0", ok)
check("(B) the discriminant of (139), 32x^4 - 16x^2 + 1, is 2^23 (Sylvester and (1.35))",
      disc_gkz([1, 0, -16, 0, 32]) == 2 ** 23 and gkz_quartic(1, 0, -16, 0, 32) == 2 ** 23)

# ---------------------------------------------------------------- (C) Proposition 9.5
a = 1 / arb(8).sqrt()
kB = qball(Q(1380649, 10 ** 29))                       # 1.380649e-23 J/K, exact
for label, muB in (("mu_B = 9.274e-24", qball(Q(9274, 10 ** 27))),
                   ("mu_B = 9.2740100783e-24 (CODATA 2018)", qball(Q(92740100783, 10 ** 34)))):
    ratio = a * kB / muB
    check(f"(C) {label}: a k_B/mu_B rounds to 0.526 T/K", rounds_to(ratio, Q(526, 1000), Q(5, 10000)))
    T2 = muB * 2 / (kB * a)
    check(f"(C) {label}: |B| = 2 T gives x = a at T rounding to 3.80 K", rounds_to(T2, Q(380, 100), Q(5, 1000)))
    Tex = 2 * muB * 2 / (kB * arb(2).log())
    check(f"(C) {label}: Exercise 11.8, ratio 2 at 2 T, T = 2 mu_B |B|/(k_B log 2) rounds to 3.88 K",
          rounds_to(Tex, Q(388, 100), Q(5, 1000)))
check("(C) 2a = 1/sqrt2 and e^(2a) = e^(1/sqrt2) rounds to 2.028",
      (2 * a - 1 / arb(2).sqrt()).contains(0) and rounds_to((2 * a).exp(), Q(2028, 1000), Q(5, 10000)))
check("(C) the population ratio of two levels -+x is e^(2x): e^(a)/e^(-a) = e^(2a)",
      ((a.exp() / (-a).exp()) - (2 * a).exp()).contains(0))

# ---------------------------------------------------------------- (D) Proposition 8.6, the line of loops
ok = True
for Lq, Cq, Mq in ((Q(1), Q(1), Q(1, 20)), (Q(50, 10 ** 9), Q(1, 10 ** 10), Q(3, 10 ** 9)), (Q(2), Q(3), Q(-1, 7))):
    kappa = 2 * Mq / Lq
    w02 = 1 / (Lq * Cq)
    for c in (Q(1), Q(1, 2), Q(-1, 3), Q(0), Q(-1)):
        if 1 + kappa * c <= 0:
            continue
        w2 = w02 / (1 + kappa * c)
        # j w L + 1/(j w C) + 2 j w M c = (j/w)[w^2 (L + 2 M c) - 1/C]
        ok = ok and w2 * (Lq + 2 * Mq * c) - 1 / Cq == 0
check("(D) Z_0 + 2 j w M c = 0 exactly when w_0^2/w^2 = 1 + kappa c, kappa = 2M/L (three lines, five c)", ok)
pi = arb.pi()
mu = (2 + arb(2).sqrt()).sqrt()
check("(D) seven loops: 2 cos(pi/8) = mu_hex and 2 cos(7 pi/8) = -mu_hex",
      (2 * (pi / 8).cos() - mu).contains(0) and (2 * (7 * pi / 8).cos() + mu).contains(0))


# ---------------------------------------------------------------- (E) Section 9
class G:
    """Gaussian rationals x + i y."""
    def __init__(s, x, y=0):
        s.x, s.y = Q(x), Q(y)

    def __add__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.x + o.x, s.y + o.y)

    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.x - o.x, s.y - o.y)

    def __mul__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.x * o.x - s.y * o.y, s.x * o.y + s.y * o.x)

    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, G) else G(o)
        n = o.x * o.x + o.y * o.y
        return G((s.x * o.x + s.y * o.y) / n, (s.y * o.x - s.x * o.y) / n)

    def conj(s):
        return G(s.x, -s.y)

    def __eq__(s, o):
        o = o if isinstance(o, G) else G(o)
        return s.x == o.x and s.y == o.y


I_ = G(0, 1)


def mm(A, B):
    return [[A[i][0] * B[0][j] + A[i][1] * B[1][j] for j in range(2)] for i in range(2)]


def smul(c, A):
    return [[c * A[i][j] for j in range(2)] for i in range(2)]


def meq(A, B):
    return all(A[i][j] == B[i][j] for i in range(2) for j in range(2))


s1 = [[G(0), G(1)], [G(1), G(0)]]
s2 = [[G(0), G(0, -1)], [G(0, 1), G(0)]]
s3 = [[G(1), G(0)], [G(0), G(-1)]]
e1 = [[G(0), G(0, -1)], [G(0, -1), G(0)]]           # (12.82)
e2 = [[G(0), G(-1)], [G(1), G(0)]]
e3 = [[G(0, -1), G(0)], [G(0), G(0, 1)]]
mI = [[G(-1), G(0)], [G(0), G(-1)]]
check("(E) U = -i sigma_2 = e_2 = [[0, -1], [1, 0]] of (12.82)", meq(smul(G(0, -1), s2), e2))
check("(E) e_1 = -i sigma_1 and e_3 = -i sigma_3", meq(smul(G(0, -1), s1), e1) and meq(smul(G(0, -1), s3), e3))
check("(E) e_1^2 = e_2^2 = e_3^2 = -I and e_1 e_2 = e_3, e_2 e_3 = e_1, e_3 e_1 = e_2",
      all(meq(mm(e, e), mI) for e in (e1, e2, e3)) and meq(mm(e1, e2), e3) and meq(mm(e2, e3), e1)
      and meq(mm(e3, e1), e2))

ok = ok_chart = True
for _ in range(30):
    z1 = G(random.randint(-6, 6), random.randint(-6, 6))
    z2 = G(random.randint(-6, 6), random.randint(-6, 6))
    if z1 == 0:
        continue
    nn = (z1 * z1.conj() + z2 * z2.conj()).x
    # psi^dagger sigma_k psi with psi = (z1, z2)
    b1 = (z1.conj() * z2 + z2.conj() * z1).x
    b2 = (z1.conj() * (G(0, -1) * z2) + z2.conj() * (G(0, 1) * z1)).x
    b3 = (z1 * z1.conj() - z2 * z2.conj()).x
    hopf = z1.conj() * z2 * 2
    ok = ok and hopf == G(b1, b2) and b3 == (z1 * z1.conj()).x - (z2 * z2.conj()).x
    w1, w2, w3 = b1 / nn, b2 / nn, b3 / nn
    ok_chart = ok_chart and (G(w1, w2) / G(1 + w3)) == z2 / z1
check("(E) Hopf projection (2 conj(z1) z2, |z1|^2 - |z2|^2) = psi^dagger sigma psi of (151) (30 Gaussian points)", ok)
check("(E) the chart (omega_1 + i omega_2)/(1 + omega_3) of the Bloch vector returns z2/z1 (30 points)", ok_chart)

if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    for f_ in failures:
        print("  FAIL:", f_)
    sys.exit(1)
print(f"ALL {count} VERSION-14.92 ADDITION CHECKS PASSED (precision {ctx.prec} bits)")
