#!/usr/bin/env python3
"""Manuscript 14, versions 14.95-14.104 of 8 November 2026: certificates of the changes.

Exact rational and Q(sqrt2) arithmetic and Arb balls at 2000 bits (python-flint 0.9.0) for the
displays added or rewritten in versions 14.95-14.104 (equation numbers of version 14.104):

  (A) Proposition 8.7, (141)-(142): the root x_0 is computed by four independent routes,
      mu_hex/sqrt8, (1/pi) int_{-oo}^{oo} dt/(1 + t^8) by rigorous Arb integration of
      2 int_0^1 (1 + u^6)/(1 + u^8) du, (1/2) sqrt(1 + 1/sqrt2) and 1/(4 sin(pi/8)); the 50 decimals
      printed in (142) are exact, by truncation (the 51st decimal is 4).
  (B) Proposition 8.7, (139)-(140), (147): the monic form x^4 - x^2/2 + 1/32 of (139); 32 times it is
      the integer form 32x^4 - 16x^2 + 1 of the proof; its roots are +-x_0, +-x_1 with
      x_0^2 = (2 + sqrt2)/8, x_1^2 = (2 - sqrt2)/8 = 1/(2 mu_hex)^2 (exact in Q(sqrt2)); (140);
      x_0/x_1 = 1 + sqrt2 = cot(pi/8); its discriminant R(f, f')/a_n is 1/128 = 2^23/32^6, by the
      Sylvester determinant, by the quartic formula (1.35) of Gelfand-Kapranov-Zelevinsky and, in
      Arb, by the product of the squared differences of the four roots.
  (C) Proposition 8.7, (143)-(148): with s_PT^2 = 2(2 - gamma_PT^2) (145) and
      g_PT^2 = 1 - [(2 - gamma_PT^2)/sqrt8]^2 (146), P_PT(s_PT x) = s_PT^4 (x^4 - x^2/2 + 1/32) (144)
      coefficientwise for seven rational gamma_PT^2 in [0, 2); the discriminant of P_PT is s_PT^12 times
      that of (139), i.e. s_PT^12/128; the four frequencies s_PT x_k are roots of P_PT; (148).
  (D) Proposition 8.4, (126)-(127): K_sd = log(1 + sqrt2)/2 satisfies sinh 2K_sd = 1 and agrees with
      the 50 printed decimals of (127) to within 10^-50.
  (E) Proposition 8.6, (137): (|z_0|/4) mu_hex sqrt(2 + mu_hex) = |z_0| (mu_hex/2) (sqrt(2 + mu_hex)/2)
      = cos(pi/4) cos(pi/8) cos(pi/16) = 1/(8 sin(pi/16)), the first three factors of Viete's product.
  (F) Proposition 8.4, (128)-(129): zeta(1/2) < 0 and L_2(1/2, chi_1) = 2^(-1/2) zeta(1/2, 1/2), the
      Hurwitz zeta function at s = a = 1/2 (Arb's analytic continuation, independent of the closed
      form), equals (1 - 2^(-1/2)) zeta(1/2), the entry m = 2, r = 1 of Table 22 of Mathar at s = 1/2;
      the same Hurwitz route reproduces the entries s = 2, 3, 4 of that table (pi^2/8, 7 zeta(3)/8,
      pi^4/96); hence 1 - L_2/zeta = 1/sqrt2 (128) and 1/2 - L_2/zeta = (sqrt2 - 1)/2 (129); the
      integral (1/pi) int_{-pi/2}^{pi/2} dtheta/(1 + sin^2 theta) of (128) is 1/sqrt2; 1 + G_* =
      (1 + sqrt2)/2 has the first 30 digits 1, 2, 0, 7, 1, 0, ... of OEIS A174968.
"""
from fractions import Fraction as Q
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
z0abs = 1 / s2
mu = (2 + s2).sqrt()
half = arb(1) / 2


# ------------------------------------------------------------- exact Q(sqrt2) arithmetic
class R2:
    """x + y sqrt2 with rational x, y."""

    def __init__(s, x, y=0):
        s.x, s.y = Q(x), Q(y)

    def __add__(s, o):
        o = o if isinstance(o, R2) else R2(o); return R2(s.x + o.x, s.y + o.y)
    __radd__ = __add__

    def __neg__(s):
        return R2(-s.x, -s.y)

    def __sub__(s, o):
        return s + (-(o if isinstance(o, R2) else R2(o)))

    def __rsub__(s, o):
        return R2(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, R2) else R2(o); return R2(s.x * o.x + 2 * s.y * o.y, s.x * o.y + s.y * o.x)
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, R2) else R2(o)
        n = o.x * o.x - 2 * o.y * o.y
        return s * R2(o.x / n, -o.y / n)

    def __rtruediv__(s, o):
        return R2(o) / s

    def __pow__(s, k):
        r = R2(1)
        for _ in range(k):
            r = r * s
        return r

    def __eq__(s, o):
        o = o if isinstance(o, R2) else R2(o); return s.x == o.x and s.y == o.y


S2 = R2(0, 1)


# ------------------------------------------------------------- exact determinants
def det_exact(M):
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
                for c in range(i, n):
                    M[r][c] -= f * M[i][c]
    return d


def sylvester_low(f, g):
    m, n = len(f) - 1, len(g) - 1
    N = m + n
    rows = []
    for i in range(n):
        rows.append([0] * i + list(f) + [0] * (N - m - 1 - i))
    for i in range(m):
        rows.append([0] * i + list(g) + [0] * (N - n - 1 - i))
    return rows


def disc_gkz(f):
    """Delta(f) = R(f, f')/a_n (GKZ normalisation); f from the constant term on."""
    n = len(f) - 1
    fp = [k * f[k] for k in range(1, n + 1)]
    return det_exact(sylvester_low(f, fp)) / Q(f[-1])


def gkz_quartic(a0, a1, a2, a3, a4):
    """GKZ, Chapter 12, Eq. (1.35)."""
    return (256 * a0**3 * a4**3 - 27 * a0**2 * a3**4 - 27 * a1**4 * a4**2 + 16 * a0 * a2**4 * a4
            - 4 * a0 * a2**3 * a3**2 - 4 * a1**2 * a2**3 * a4 - 4 * a1**3 * a3**3 + a1**2 * a2**2 * a3**2
            - 192 * a0**2 * a1 * a3 * a4**2 - 128 * a0**2 * a2**2 * a4**2 + 144 * a0**2 * a2 * a3**2 * a4
            + 144 * a0 * a1**2 * a2 * a4**2 - 6 * a0 * a1**2 * a3**2 * a4 - 80 * a0 * a1 * a2**2 * a3 * a4
            + 18 * a0 * a1 * a2 * a3**3 + 18 * a1**3 * a2 * a3 * a4)


# ---------------------------------------------------------------- (A) (141)-(142)
x0a = mu / arb(8).sqrt()
J = acb.integral(lambda u, analytic: (1 + u ** 6) / (1 + u ** 8), acb(0), acb(1))
x0b = 2 * J.real / pi
x0c = (1 + 1 / s2).sqrt() / 2
x0d = 1 / (4 * (pi / 8).sin())
check("(A) (141): mu_hex/sqrt8 = (1/pi) int dt/(1+t^8) (Arb integral of 2(1+u^6)/(1+u^8) on [0,1])",
      is_zero_ball(x0a - x0b))
check("(A) (141): mu_hex/sqrt8 = (1/2) sqrt(1 + 1/sqrt2) = 1/(4 sin(pi/8))",
      is_zero_ball(x0a - x0c) and is_zero_ball(x0a - x0d))
printed142 = "65328148243818826392832158671359357679188059417463"
check("(A) (142) prints 50 decimals", len(printed142) == 50)
P = Q(int(printed142), 10 ** 50)
x0 = x0c
check("(A) (142): 0.65328148243818826392832158671359357679188059417463 <= x_0 < it + 10^-50 (50 exact decimals)",
      bool(x0 > qball(P)) and bool(x0 < qball(P + Q(1, 10 ** 50))))
check("(A) (142): the 51st decimal of x_0 is 4 (truncation, not rounding up)",
      bool(x0 > qball(P + Q(4, 10 ** 51))) and bool(x0 < qball(P + Q(5, 10 ** 51))))

# ---------------------------------------------------------------- (B) (139)-(140), (147)
monic = [Q(1, 32), Q(0), Q(-1, 2), Q(0), Q(1)]          # x^4 - x^2/2 + 1/32, constant term first
integer = [1, 0, -16, 0, 32]
check("(B) 32 (x^4 - x^2/2 + 1/32) = 32x^4 - 16x^2 + 1 coefficientwise", [32 * c for c in monic] == integer)
y0, y1 = (2 + S2) / 8, (2 - S2) / 8
check("(B) (139): y^2 - y/2 + 1/32 = 0 at y = x_0^2 = (2+sqrt2)/8 and y = x_1^2 = (2-sqrt2)/8 (exact)",
      y0 * y0 - y0 / 2 + R2(Q(1, 32)) == 0 and y1 * y1 - y1 / 2 + R2(Q(1, 32)) == 0)
check("(B) (140): x_1^2 = 1/(2 mu_hex)^2 = 1/(4(2+sqrt2)) = (2-sqrt2)/8 (exact)", R2(1) / (4 * (2 + S2)) == y1)
check("(B) (140): x_0^2 - x_1^2 = sqrt2/4 = a > 0, (2 x_0 x_1)^2 = 4 x_0^2 x_1^2 = 1/8 = a^2 (exact)",
      y0 - y1 == S2 / 4 and (S2 / 4) ** 2 == R2(Q(1, 8)) and 4 * y0 * y1 == R2(Q(1, 8)))
check("(B) (140)-(141): x_0^2 = mu_hex^2/8 = (1 + 1/sqrt2)/4 (exact)", (2 + S2) / 8 == y0 and (1 + R2(1) / S2) / 4 == y0)
x1 = 1 / (2 * mu)


def mon(x):
    return x ** 4 - x ** 2 / 2 + qball(Q(1, 32))


check("(B) (139) in Arb: the monic quartic vanishes at x_0, x_1, -x_1, -x_0",
      all(is_zero_ball(mon(r)) for r in (x0, x1, -x1, -x0)))
check("(B) x_0 > x_1 > 0 and x_0^2 - x_1^2 = 2 x_0 x_1 = a in Arb",
      bool(x0 > x1) and bool(x1 > 0) and is_zero_ball(x0 ** 2 - x1 ** 2 - a) and is_zero_ball(2 * x0 * x1 - a))
check("(B) (147): x_0/x_1 = 1 + sqrt2 = cot(pi/8) in Arb",
      is_zero_ball(x0 / x1 - 1 - s2) and is_zero_ball((pi / 8).cos() / (pi / 8).sin() - 1 - s2))
d_syl = disc_gkz(monic)
check("(B) discriminant of (139): Sylvester R(f,f')/a_4 = 1/128", d_syl == Q(1, 128))
check("(B) discriminant of (139): GKZ (1.35) = 1/128 = 2^23/32^6, and 2^23 for 32x^4 - 16x^2 + 1",
      gkz_quartic(*monic) == Q(1, 128) and Q(1, 128) == Q(2 ** 23, 32 ** 6)
      and gkz_quartic(*[Q(c) for c in integer]) == 2 ** 23 and disc_gkz(integer) == 2 ** 23)
roots = [x0, x1, -x1, -x0]
prod = arb(1)
for i in range(4):
    for j in range(i + 1, 4):
        prod *= (roots[i] - roots[j]) ** 2
check("(B) discriminant of (139) in Arb: prod_{i<j} (r_i - r_j)^2 = 1/128", is_zero_ball(prod - qball(Q(1, 128))))

# ---------------------------------------------------------------- (C) (143)-(148)
ok_coef = ok_scale = ok_coupl = ok_disc = True
for g2 in [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(3, 2), Q(7, 4), Q(199, 100)]:
    s2_ = 2 * (2 - g2)                                    # (145)
    ok_scale = ok_scale and s2_ == 4 - 2 * g2 and s2_ > 0
    gg = 1 - (2 - g2) ** 2 / 8                            # (146), exact
    ok_coupl = ok_coupl and is_zero_ball(1 - ((qball(2 - g2)) / arb(8).sqrt()) ** 2 - qball(gg))
    lhs = [1 - gg, 0, (g2 - 2) * s2_, 0, s2_ * s2_]      # P_PT(s x), constant term first
    rhs = [s2_ * s2_ * c for c in monic]                 # s^4 (x^4 - x^2/2 + 1/32)
    ok_coef = ok_coef and lhs == rhs
    ok_disc = ok_disc and gkz_quartic(1 - gg, 0, g2 - 2, 0, Q(1)) == s2_ ** 6 * Q(1, 128) \
        and disc_gkz([1 - gg, 0, g2 - 2, 0, 1]) == s2_ ** 6 * Q(1, 128)
check("(C) (145): s_PT^2 = 2(2 - gamma_PT^2) = 4 - 2 gamma_PT^2 > 0 for seven gamma_PT^2 in [0, 2)", ok_scale)
check("(C) (146): 1 - [(2 - gamma_PT^2)/sqrt8]^2 = 1 - (2 - gamma_PT^2)^2/8 in Arb, seven values", ok_coupl)
check("(C) (144): P_PT(s_PT x) = s_PT^4 (x^4 - x^2/2 + 1/32) coefficientwise, seven values", ok_coef)
check("(C) discriminant of P_PT = s_PT^12 x (1/128) = s_PT^12/128 (GKZ (1.35) and Sylvester), seven values", ok_disc)
g2 = Q(1, 2)
s = qball(2 * (2 - g2)).sqrt()
gg = qball(1 - (2 - g2) ** 2 / 8)


def P_PT(y):
    return y ** 4 + (qball(g2) - 2) * y ** 2 + 1 - gg


check("(C) the four frequencies s_PT x_k are roots of P_PT (Arb, gamma_PT^2 = 1/2)",
      all(is_zero_ball(P_PT(s * r)) for r in roots))
check("(C) (148): at gamma_PT = 0, s_PT^2 = 4 and g_PT^2 = 1 - (2/sqrt8)^2 = 1/2 = |z_0|^2",
      2 * (2 - 0) == 4 and is_zero_ball(1 - (2 / arb(8).sqrt()) ** 2 - z0abs ** 2) and is_zero_ball(z0abs ** 2 - half))

# ---------------------------------------------------------------- (D) (126)-(127)
K = (1 + s2).log() / 2
P127 = Q(44068679350977151261630466248989615451408016413082, 10 ** 50)
check("(D) (126): K_sd = log(1 + sqrt2)/2 satisfies sinh 2K_sd = 1", is_zero_ball((2 * K).sinh() - 1))
check("(D) (127): |K_sd - 0.44068679350977151261630466248989615451408016413082| < 10^-50",
      bool(abs(K - qball(P127)) < qball(Q(1, 10 ** 50))))

# ---------------------------------------------------------------- (E) (137)
V = z0abs / 4 * mu * (2 + mu).sqrt()
check("(E) (137): (|z_0|/4) mu_hex sqrt(2 + mu_hex) = |z_0| (mu_hex/2) (sqrt(2 + mu_hex)/2)",
      is_zero_ball(V - z0abs * (mu / 2) * ((2 + mu).sqrt() / 2)))
check("(E) (137): it is cos(pi/4) cos(pi/8) cos(pi/16) = 1/(8 sin(pi/16)), three factors of Viete's product",
      is_zero_ball(V - (pi / 4).cos() * (pi / 8).cos() * (pi / 16).cos()) and is_zero_ball(V - 1 / (8 * (pi / 16).sin())))

# ---------------------------------------------------------------- (F) (128)-(129)
zh = half.zeta()
check("(F) zeta(1/2) < 0, in particular zeta(1/2) != 0", bool(zh < 0))
L2 = arb(2) ** (-half) * half.zeta(half)                  # sum over odd n of n^(-s), continued: 2^-s zeta(s, 1/2)
check("(F) L_2(1/2, chi_1) = 2^(-1/2) zeta(1/2, 1/2) (Hurwitz) = (1 - 2^(-1/2)) zeta(1/2) (Mathar, Table 22)",
      is_zero_ball(L2 - (1 - 1 / s2) * zh))
ok_tab = True
for sv, val in [(2, pi ** 2 / 8), (3, 7 * arb(3).zeta() / 8), (4, pi ** 4 / 96)]:
    ok_tab = ok_tab and is_zero_ball(arb(2) ** (-sv) * arb(sv).zeta(half) - val) \
        and is_zero_ball((1 - arb(2) ** (-sv)) * arb(sv).zeta() - val)
check("(F) Table 22 of Mathar, m = 2, r = 1: s = 2, 3, 4 give pi^2/8, 7 zeta(3)/8, pi^4/96 by both routes", ok_tab)
try:
    from flint import dirichlet_char
    Ld = acb.dirichlet_l(acb(half), dirichlet_char(2, 1))
    check("(F) Arb's Dirichlet L-function of the principal character mod 2 at s = 1/2 equals L_2(1/2, chi_1)",
          is_zero_ball(Ld - acb(L2)))
except (ImportError, AttributeError, TypeError) as e:
    print(f"NOTE: Dirichlet-character interface not available in this python-flint ({type(e).__name__}); "
          "the Hurwitz route above stands")
r = L2 / zh
check("(F) (128): 1 - L_2(1/2, chi_1)/zeta(1/2) = 1/sqrt2", is_zero_ball(1 - r - 1 / s2))
check("(F) (129): 1/2 - L_2(1/2, chi_1)/zeta(1/2) = (sqrt2 - 1)/2 = 1/sqrt2 - 1/2",
      is_zero_ball(half - r - (s2 - 1) / 2) and is_zero_ball((s2 - 1) / 2 - (1 / s2 - half)))
Jnu = acb.integral(lambda t, analytic: 1 / (1 + t.sin() ** 2), acb(-pi / 2), acb(pi / 2))
check("(F) (128): int dnu_0(xi)/(1 + xi^2) = (1/pi) int_{-pi/2}^{pi/2} dtheta/(1 + sin^2 theta) = 1/sqrt2",
      is_zero_ball(Jnu.real / pi - 1 / s2) and is_zero_ball(Jnu.imag))
Gs = 1 / s2 - half
c = 1 + Gs
D30 = int("".join(str(d) for d in [1, 2, 0, 7, 1, 0, 6, 7, 8, 1, 1, 8, 6, 5, 4, 7, 5, 2, 4, 4, 0, 0, 8, 4, 4, 3, 6, 2, 1, 0]))
check("(F) 1 + G_* = (1 + sqrt2)/2 and its first 30 digits are the terms 1, 2, 0, 7, 1, 0, ... of OEIS A174968",
      is_zero_ball(c - (1 + s2) / 2) and bool(c > qball(Q(D30, 10 ** 29))) and bool(c < qball(Q(D30 + 1, 10 ** 29))))

print("x_0                 =", x0.str(60, radius=False))
print("zeta(1/2)           =", zh.str(40, radius=False))
print("L_2(1/2, chi_1)     =", L2.str(40, radius=False))
if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    for f_ in failures:
        print("  FAIL:", f_)
    sys.exit(1)
print(f"ALL {count} VERSION-14.95-14.104 CHECKS PASSED (precision {ctx.prec} bits)")
