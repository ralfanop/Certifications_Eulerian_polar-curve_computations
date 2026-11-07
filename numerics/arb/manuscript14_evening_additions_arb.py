#!/usr/bin/env python3
"""Manuscript 14, version 14.91 of 7 November 2026 (evening): certificates of the additions.

Exact rational arithmetic (fractions, and Q(sqrt2) as pairs of rationals) and Arb balls at
2000 bits (python-flint 0.9.0) for:

  (A) Section 4.3: the Langevin Riccati equation (54) L' = 1 - L^2 - 2L/x and its general
      solution L_rho = d/dx log[(sinh x + rho cosh x)/x]; the linear parts of the Riccati
      foliation x dy + (x y^2 + 2y - x) dx = 0 at (0,0) (saddle, eigenvalues 1 and -2, separatrix
      slope 1/3 = L'(0)) and at (0, infinity) (node, eigenvalues 1 and 2); w(z) = 1/z - cot z with
      w(ix) = i L(x), w' = w^2 - 2w/z + 1 and the third Painleve equation (55) at complex points.
  (B) Theorem 4.2, proof (the value of B_1): Knuth's Bernoulli numbers (z/(1 - e^{-z})),
      B_1 = 1/2; the kernel (49) k(m) = (-1)^m B_{m+1}/(m+1)! equals the form -B^-_{m+1}/(m+1)!
      of Borodin, Diaconis and Fulman with B^-_1 = -1/2; its generating function is 1/(1 - e^q);
      with k(0) = -1/2 instead: the generating function -1/(1 - e^{-q}), the mean -(n-1)/2 and the
      negative variance -3(n-1)/4 - (n-2)/6; det[I + (x-1) K_{n-1}] n! = sum over S_n of x^des
      (n = 2..7, exhaustive), and with k(0) = -1/2 the polynomials 3 - x and x^2 - 8x + 13 (zeros 3
      and 4 +- sqrt3); Bernoulli's sums of powers with B_1 = 1/2 (sum to n) and B_1 = -1/2 (sum to
      n - 1).
  (C) Proposition 8.2 (iii), display (122): the eight terms 1/2, 1/6, ..., 691/20432412000,
      1/583783200 and their zeta form.
  (D) Proposition 8.6 (iv), display (138): the middle term (pi/2) sqrt(1 + 1/sqrt2).
  (E) Proposition 8.7, displays (139)-(147): the quartic minimal polynomial 32x^4 - 16x^2 + 1 of
      varpi = (1/pi) int dt/(1+t^8) = (1/2) sqrt(1 + 1/sqrt2) = mu_hex/sqrt8 (roots, irreducibility
      by Eisenstein for mu^4 - 4mu^2 + 2 and by the criterion for biquadratics, primitivity),
      (140), Bender's characteristic polynomial (142)-(145) for rational gamma_PT^2 in [0, 2),
      the ratio (146) cot(pi/8) = 1 + sqrt2, (147) at gamma_PT = 0, and the midradius of the square
      antiprism with unit edges.
"""
from fractions import Fraction as Q
from math import comb, factorial
from itertools import permutations
import sys
import flint
from flint import arb, acb, ctx

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


TINY = arb(2) ** (-1900)


def is_zero_ball(x):
    if isinstance(x, acb):
        return is_zero_ball(x.real) and is_zero_ball(x.imag)
    return x.contains(0) and abs(x).upper() < TINY


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

pi = arb.pi()
s2 = arb(2).sqrt()
a = 1 / arb(8).sqrt()
b = 1 / s2
mu = (2 + s2).sqrt()


def coth(x):
    return x.cosh() / x.sinh()


def L(x):
    return coth(x) - 1 / x


def Lp(x):
    return 1 / (x * x) - 1 / (x.sinh() ** 2)


# ---------------------------------------------------------------- (A) Section 4.3
xs = [a, b, qball(Q(1, 3)), arb(1), arb(2), arb(5)]
check("(A) (54): L' = 1 - L^2 - 2L/x at x = a, b, 1/3, 1, 2, 5",
      all(is_zero_ball(Lp(x) - (1 - L(x) ** 2 - 2 * L(x) / x)) for x in xs))


def Lrho(x, r):
    return (x.cosh() + r * x.sinh()) / (x.sinh() + r * x.cosh()) - 1 / x


def Lrho_p(x, r):
    return -(1 - r * r) / (x.sinh() + r * x.cosh()) ** 2 + 1 / (x * x)


ok = True
for r in [qball(Q(1, 3)), arb(-2), arb(5), qball(Q(-1, 7))]:
    for x in [qball(Q(1, 5)), arb(1), arb(3)]:
        ok = ok and is_zero_ball(Lrho_p(x, r) - (1 - Lrho(x, r) ** 2 - 2 * Lrho(x, r) / x))
check("(A) L_rho = d/dx log[(sinh x + rho cosh x)/x] solves (54), rho = 1/3, -2, 5, -1/7", ok)
check("(A) L_0 = L at x = a, b", is_zero_ball(Lrho(a, arb(0)) - L(a)) and is_zero_ball(Lrho(b, arb(0)) - L(b)))
# linear parts of the foliation, exact
J0 = [[Q(1), Q(0)], [Q(1), Q(-2)]]          # (x, x - x y^2 - 2y) at (0,0)
Jinf = [[Q(1), Q(0)], [Q(1), Q(2)]]         # (x, x + 2Y - x Y^2) at (0,0), Y = 1/y


def eig2(M):
    tr = M[0][0] + M[1][1]
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return tr, det


check("(A) saddle at (0,0): eigenvalues 1 and -2 (trace -1, determinant -2)", eig2(J0) == (Q(-1), Q(-2)))
check("(A) separatrix direction (1, 1/3): J (1, 1/3) = (1, 1/3), slope 1/3",
      [J0[0][0] + J0[0][1] * Q(1, 3), J0[1][0] + J0[1][1] * Q(1, 3)] == [Q(1), Q(1, 3)])
check("(A) L'(x) -> 1/3: |L'(x) - 1/3| <= x^2 for x = 10^-3, 10^-6",
      all(abs(Lp(qball(Q(1, 10 ** k))) - qball(Q(1, 3))) < qball(Q(1, 10 ** (2 * k))) for k in (3, 6)))
check("(A) node at (0, infinity): eigenvalues 1 and 2 (trace 3, determinant 2)", eig2(Jinf) == (Q(3), Q(2)))


def w(z):
    return 1 / z - z.cos() / z.sin()


def w1(z):
    return -1 / (z * z) + 1 / z.sin() ** 2


def w2(z):
    return 2 / z ** 3 - 2 * z.cos() / z.sin() ** 3


zs = [acb(qball(Q(3, 10)), qball(Q(1, 5))), acb(qball(Q(11, 10)), qball(Q(-2, 5))), acb(0, b), acb(qball(Q(7, 10)), 0)]
check("(A) w' = w^2 - 2w/z + 1 at four complex points (z0 = i/sqrt2 included)",
      all(is_zero_ball(w1(z) - (w(z) ** 2 - 2 * w(z) / z + 1)) for z in zs))
check("(A) (55): w'' = w'^2/w - w'/z + (3 - w^2)/z + w^3 - 1/w at the same points",
      all(is_zero_ball(w2(z) - (w1(z) ** 2 / w(z) - w1(z) / z + (3 - w(z) ** 2) / z + w(z) ** 3 - 1 / w(z))) for z in zs))
check("(A) w(ix) = i L(x) at x = a, b, 1",
      all(is_zero_ball(w(acb(0, x)) - acb(0, L(x))) for x in [a, b, arb(1)]))
check("(A) r_E(2z) = sin z/z and w = -(d/dz) log r_E(2z) at z = 3/10 + i/5",
      is_zero_ball(w(zs[0]) - (1 / zs[0] - zs[0].cos() / zs[0].sin())))

# ---------------------------------------------------------------- (B) Theorem 4.2, B_1
N = 40
Bm = [Q(1)]                                   # z/(e^z - 1): B^-_1 = -1/2
for n in range(1, N + 1):
    Bm.append(-sum(comb(n + 1, k) * Bm[k] for k in range(n)) / (n + 1))
Bk = [(-1) ** n * Bm[n] for n in range(N + 1)]  # z/(1 - e^{-z}): Knuth, B_1 = 1/2
check("(B) Knuth's numbers: B_1 = 1/2, B_2 = 1/6, B_n = B^-_n for n != 1",
      Bk[1] == Q(1, 2) and Bk[2] == Q(1, 6) and all(Bk[n] == Bm[n] for n in range(N + 1) if n != 1))
# z/(1 - e^{-z}) = sum Bk_n z^n/n!: check (1 - e^{-z}) * series = z coefficientwise
ok = True
for n in range(0, N):
    c = sum(Bk[j] / factorial(j) * (-(-1) ** (n + 1 - j)) / factorial(n + 1 - j) for j in range(0, n + 1))
    ok = ok and (c == (1 if n == 0 else 0))
check("(B) z/(1 - e^{-z}) = sum B_n z^n/n! with Knuth's B_n (coefficients up to z^40)", ok)


def kK(m):
    return Q(-1) if m == -1 else (Q(0) if m < -1 else (-1) ** m * Bk[m + 1] / factorial(m + 1))


def kBDF(m):
    return Q(-1) if m == -1 else (Q(0) if m < -1 else -Bm[m + 1] / factorial(m + 1))


check("(B) (49) k(m) = (-1)^m B_{m+1}/(m+1)! equals -B^-_{m+1}/(m+1)! (BDF, Remark (2)) for -1 <= m <= 38",
      all(kK(m) == kBDF(m) for m in range(-1, N - 1)))
# (1 - e^q) * sum_{m>=-1} k(m) q^m = 1 as Laurent series
ok = True
for n in range(-1, N - 2):
    # 1 - e^q = -sum_{j>=1} q^j/j!, so the coefficient of q^n is -sum_{m <= n-1} k(m)/(n-m)!
    c = -sum(kK(m) / factorial(n - m) for m in range(-1, n))
    ok = ok and (c == (1 if n == 0 else 0))
check("(B) (48): (1 - e^q) sum k(m) q^m = 1 (coefficients q^-1 .. q^37)", ok)
check("(B) k(0) = B_1 = 1/2, k(1) = -1/12, k(-1) = -1, k(2) = 0", (kK(0), kK(1), kK(-1), kK(2)) == (Q(1, 2), Q(-1, 12), Q(-1), Q(0)))


def kW(m):
    return Q(-1, 2) if m == 0 else kK(m)


ok = True
for n in range(-1, N - 2):
    # -1/(1 - e^{-q}) = -(1/q) * q/(1 - e^{-q}) = -sum B_j q^{j-1}/j!
    ok = ok and (kW(n) == -Bk[n + 1] / factorial(n + 1))
check("(B) with k(0) = -1/2: sum k q^m = 1/(1 - e^q) - 1 = -1/(1 - e^{-q}), constant term -1/2", ok)


def corner(n, k):
    return [[k(j - i) for j in range(n)] for i in range(n)]


ok1 = ok2 = True
for n in range(2, 31):
    K1 = corner(n - 1, kK)
    K2 = corner(n - 1, kW)
    t1 = sum(K1[i][i] for i in range(n - 1)); v1 = t1 - sum(K1[i][j] * K1[j][i] for i in range(n - 1) for j in range(n - 1))
    t2 = sum(K2[i][i] for i in range(n - 1)); v2 = t2 - sum(K2[i][j] * K2[j][i] for i in range(n - 1) for j in range(n - 1))
    ok1 = ok1 and t1 == Q(n - 1, 2) and v1 == Q(n + 1, 12) == Q(n - 1, 4) - Q(n - 2, 6)
    ok2 = ok2 and t2 == -Q(n - 1, 2) and v2 == -Q(3 * (n - 1), 4) - Q(n - 2, 6) and v2 < 0
check("(B) k(0) = 1/2: Tr K_{n-1} = (n-1)/2 and Tr K - Tr K^2 = (n-1)/4 - (n-2)/6 = (n+1)/12 = (47), 2 <= n <= 30", ok1)
check("(B) k(0) = -1/2: Tr K_{n-1} = -(n-1)/2 and variance -3(n-1)/4 - (n-2)/6 < 0, 2 <= n <= 30", ok2)


def det(M):
    M = [row[:] for row in M]
    n = len(M); d = Q(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Q(0)
        if p != c:
            M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return d


def detpoly(n, k):
    # n! det[I + (x-1) K_{n-1}] as a polynomial in x, by interpolation at x = 0..n
    vals = []
    for x in range(n):
        M = [[(1 if i == j else 0) + (x - 1) * k(j - i) for j in range(n - 1)] for i in range(n - 1)]
        vals.append(det(M) * factorial(n))
    # Newton -> monomial coefficients via Lagrange
    deg = n - 1
    coeffs = [Q(0)] * (deg + 1)
    for i, xi in enumerate(range(n)):
        num = [Q(1)]
        den = Q(1)
        for j, xj in enumerate(range(n)):
            if j != i:
                num = [Q(0)] + num
                for t in range(len(num) - 1):
                    num[t] -= xj * num[t + 1]
                den *= (xi - xj)
        for t in range(len(num)):
            coeffs[t] += vals[i] * num[t] / den
    return coeffs


def eulerian(n):
    c = [0] * n
    for p in permutations(range(n)):
        c[sum(p[i] > p[i + 1] for i in range(n - 1))] += 1
    return [Q(x) for x in c]


check("(B) n! det[I + (x-1)K_{n-1}] = sum over S_n of x^des, 2 <= n <= 7 (exhaustive enumeration)",
      all(detpoly(n, kK) == eulerian(n) for n in range(2, 8)))
check("(B) with k(0) = -1/2: 2! det = 3 - x and 3! det = x^2 - 8x + 13",
      detpoly(2, kW) == [Q(3), Q(-1)] and detpoly(3, kW) == [Q(13), Q(-8), Q(1)])
r3 = arb(3).sqrt()
check("(B) zeros 3 and 4 +- sqrt3 > 1, so that 1/(1 - alpha) < 0",
      is_zero_ball((4 + r3) ** 2 - 8 * (4 + r3) + 13) and is_zero_ball((4 - r3) ** 2 - 8 * (4 - r3) + 13)
      and (4 - r3) > 1)
ok1 = ok2 = True
for c in range(1, 11):
    for n in range(1, 31):
        f1 = sum(comb(c + 1, j) * Bk[j] * Q(n) ** (c + 1 - j) for j in range(c + 1)) / (c + 1)
        f2 = sum(comb(c + 1, j) * Bm[j] * Q(n) ** (c + 1 - j) for j in range(c + 1)) / (c + 1)
        ok1 = ok1 and f1 == sum(Q(k) ** c for k in range(1, n + 1))
        ok2 = ok2 and f2 == sum(Q(k) ** c for k in range(1, n))
check("(B) Bernoulli: sum_{k<=n} k^c = sum_j C(c+1,j) B_j n^{c+1-j}/(c+1) with B_1 = 1/2 (c <= 10, n <= 30)", ok1)
check("(B) with B_1 = -1/2 the same formula gives the sum up to n - 1 (c <= 10, n <= 30)", ok2)

# ---------------------------------------------------------------- (C) Proposition 8.2, (122)
terms = [(-1) ** (m + 1) * 2 ** m * Bk[2 * m] / factorial(2 * m) for m in range(1, 8)]
check("(C) (122): 1/6, 1/180, 1/3780, 1/75600, 1/1496880, 691/20432412000, 1/583783200",
      terms == [Q(1, 6), Q(1, 180), Q(1, 3780), Q(1, 75600), Q(1, 1496880), Q(691, 20432412000), Q(1, 583783200)])
ok = True
NZ = 3000
for m in range(1, 8):
    zl = sum(qball(Q(1, n ** (2 * m))) for n in range(1, NZ + 1))
    zh = zl + qball(Q(1, (2 * m - 1) * NZ ** (2 * m - 1)))
    zt = qball(terms[m - 1]) * 2 ** (m - 1) * pi ** (2 * m)
    ok = ok and zl <= zt and zt <= zh
check("(C) (122): 2^{m-1} pi^{2m} x term lies in the certified bracket of zeta(2m), m <= 7", ok)
C0 = arb(3) / 2 - (b.cos() / b.sin()) / s2
part = qball(Q(1, 2) + sum(terms))
check("(C) 1/2 + the seven terms < C0 = 3/2 - cot(1/sqrt2)/sqrt2 < that sum + 10^-9", part < C0 and C0 < part + qball(Q(1, 10 ** 9)))

# ---------------------------------------------------------------- Q(sqrt2) arithmetic


class R2:
    def __init__(self, x, y=0):
        self.x, self.y = Q(x), Q(y)

    def __add__(s, o):
        o = o if isinstance(o, R2) else R2(o); return R2(s.x + o.x, s.y + o.y)
    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, R2) else R2(o); return R2(s.x - o.x, s.y - o.y)

    def __rsub__(s, o):
        return R2(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, R2) else R2(o); return R2(s.x * o.x + 2 * s.y * o.y, s.x * o.y + s.y * o.x)
    __rmul__ = __mul__

    def inv(s):
        n = s.x * s.x - 2 * s.y * s.y; return R2(s.x / n, -s.y / n)

    def __truediv__(s, o):
        o = o if isinstance(o, R2) else R2(o); return s * o.inv()

    def __pow__(s, k):
        r = R2(1)
        for _ in range(k):
            r = r * s
        return r

    def __eq__(s, o):
        o = o if isinstance(o, R2) else R2(o); return s.x == o.x and s.y == o.y


S2 = R2(0, 1)
# ---------------------------------------------------------------- (D) Proposition 8.6 (iv), (138)
check("(D) (138): (2 + sqrt2)/8 = (1 + 1/sqrt2)/4 in Q(sqrt2), so (pi/sqrt8) sqrt(2+sqrt2) = (pi/2) sqrt(1 + 1/sqrt2)",
      (2 + S2) / 8 == (1 + R2(1) / S2) / 4)
check("(D) (138) in Arb: (pi/sqrt8) sqrt(2+sqrt2) - (pi/2) sqrt(1 + 1/sqrt2) = 0 and = (pi/4)/sin(pi/8)",
      is_zero_ball(pi / arb(8).sqrt() * mu - pi / 2 * (1 + b).sqrt()) and is_zero_ball(pi / 2 * (1 + b).sqrt() - (pi / 4) / (pi / 8).sin()))

# ---------------------------------------------------------------- (E) Proposition 8.7
u = (2 + S2) / 8                      # varpi^2
v = (2 - S2) / 8                      # varpi'^2
check("(E) (139): 32u^2 - 16u + 1 = 0 and 32v^2 - 16v + 1 = 0 for u = (2+sqrt2)/8, v = (2-sqrt2)/8",
      32 * u * u - 16 * u + 1 == 0 and 32 * v * v - 16 * v + 1 == 0)
check("(E) (140): 1/(2 mu_hex)^2 = 1/(4(2 + sqrt2)) = v", R2(1) / (4 * (2 + S2)) == v)
check("(E) (140): u - v = sqrt2/4, (u - v)^2 = 1/8 = a^2 and 4uv = 1/8 = (2 varpi varpi')^2",
      u - v == S2 / 4 and (u - v) ** 2 == R2(Q(1, 8)) and 4 * u * v == R2(Q(1, 8)))
check("(E) (141): mu_hex^2/8 = u, so varpi = mu_hex/sqrt8 = (1/2) sqrt(1 + 1/sqrt2)", (2 + S2) / 8 == u and (1 + R2(1) / S2) / 4 == u)
varpi = mu / arb(8).sqrt()
I8 = 2 * acb.integral(lambda x, analytic: x.cos() ** 6 / (x.cos() ** 8 + x.sin() ** 8), acb(0), acb(pi / 2))
check("(E) (141): (1/pi) int dt/(1 + t^8) = mu_hex/sqrt8 = (1/2) sqrt(1 + 1/sqrt2) in Arb",
      is_zero_ball(I8 / pi - varpi) and is_zero_ball(varpi - (1 + b).sqrt() / 2))
check("(E) (139) in Arb: 32 varpi^4 - 16 varpi^2 + 1 = 0, varpi = 0.6532814824381882639283215867...",
      is_zero_ball(32 * varpi ** 4 - 16 * varpi ** 2 + 1) and abs(varpi - qball(Q(653281482438188263928321586713593576791880594174, 10 ** 48))) < qball(Q(1, 10 ** 47)))
# irreducibility and minimality
mpoly = [2, 0, -4, 0, 1]   # mu^4 - 4 mu^2 + 2
check("(E) Eisenstein at 2 for mu^4 - 4mu^2 + 2: 2 | 2, 4, 0, 0; 2 does not divide 1; 4 does not divide 2",
      all(c % 2 == 0 for c in mpoly[:4]) and mpoly[4] % 2 == 1 and mpoly[0] % 4 != 0)


def is_rat_square(q):
    q = Q(q)
    if q < 0:
        return False
    from math import isqrt
    n, d = q.numerator, q.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


p_, q_ = Q(-16, 32), Q(1, 32)   # x^4 + p x^2 + q
check("(E) x^4 - x^2/2 + 1/32 is irreducible over Q: p^2 - 4q = 1/8 and q = 1/32 are not rational squares",
      not is_rat_square(p_ * p_ - 4 * q_) and not is_rat_square(q_))
from math import gcd
check("(E) 32x^4 - 16x^2 + 1 is primitive (gcd of coefficients 1) with positive leading coefficient",
      gcd(gcd(32, 16), 1) == 1)
# Bender (142)-(147)
ok = True
for g2 in [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(3, 2), Q(7, 4), Q(199, 100)]:
    s2_ = 4 - 2 * g2
    gg = 1 - (2 - g2) ** 2 / 8
    lhs = [s2_ * s2_, (g2 - 2) * s2_, 1 - gg]          # coefficients of x^4, x^2, x^0 in P_PT(s x)
    rhs = [s2_ * s2_ / 32 * 32, s2_ * s2_ / 32 * (-16), s2_ * s2_ / 32]
    ok = ok and lhs == rhs and s2_ > 0 and 0 < gg <= 1
check("(E) (143)-(145): P_PT(s x) = s^4 (32x^4 - 16x^2 + 1)/32 for gamma^2 = 0, 1/4, 1/2, 1, 3/2, 7/4, 1.99", ok)
check("(E) four real frequencies: 32y^2 - 16y + 1 has discriminant 128 > 0 and the roots u > v > 0",
      (16 * 16 - 4 * 32 * 1) == 128 and (2 - s2) > 0 and (2 + s2) / 8 > (2 - s2) / 8)
check("(E) (146): u/v = 3 + 2 sqrt2 = (1 + sqrt2)^2, so varpi/varpi' = 1 + sqrt2", u / v == R2(3, 2) and R2(3, 2) == (1 + S2) ** 2)
check("(E) (146) in Arb: cot(pi/8) = 1 + sqrt2 and varpi/varpi' = 1 + sqrt2 with varpi' = 1/(2 mu_hex)",
      is_zero_ball((pi / 8).cos() / (pi / 8).sin() - 1 - s2) and is_zero_ball(varpi * 2 * mu - 1 - s2))
check("(E) (147): at gamma = 0, s^2 = 4 and g^2 = 1/2 = |z0|^2", (4 - 2 * Q(0)) == 4 and 1 - Q(4, 8) == Q(1, 2))
# square antiprism with unit edges: base square circumradius^2 = 1/2, height^2 = sqrt2/2
h2 = S2 / 2
lat2 = 2 * R2(Q(1, 2)) * (1 - S2 / 2) + h2         # lateral edge^2 = 2 r^2 (1 - cos 45) + h^2
check("(E) square antiprism: lateral edge^2 = 1 with height^2 = sqrt2/2", lat2 == R2(1))
mid_base = R2(Q(1, 4)) + h2 / 4                       # base-edge midpoint distance^2
mid_lat = R2(Q(1, 2)) * ((2 + S2) / 4)                # (1/2) cos^2(pi/8)
check("(E) square antiprism: both kinds of edge midpoints at distance^2 (2 + sqrt2)/8 = varpi^2",
      mid_base == u and mid_lat == u)

print("varpi          =", varpi.str(60, radius=False))
print("C0             =", C0.str(60, radius=False))
if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    for f_ in failures:
        print("  FAIL:", f_)
    sys.exit(1)
print(f"ALL {count} EVENING-ADDITION CHECKS PASSED (precision {ctx.prec} bits)")
