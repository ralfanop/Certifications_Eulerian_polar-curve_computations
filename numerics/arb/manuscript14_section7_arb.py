#!/usr/bin/env python3
"""Manuscript 14, Sections 6 and 7: Arb certificate at 2000 bits for the duplication identity.

Section 7 (Lemma 7.1, Theorem 7.2, Remark 7.5) and the spectral sums of Section 6, with
a = 1/sqrt(8), b = 1/sqrt(2) = 2a, z0 = i/sqrt(2), z1 = i sqrt(2) = 2 z0 = S z0.

  (A) Lemma 7.1: 2 z0^2 + 1 = 0, S z0 = z1 = 2 z0, S z1 = z0 (complex balls), and
      r_E(z1) - r_E(z0) = (cosh a - 1) sinh(a)/a > 0.
  (B) The exact identities (91), (94), (95), (96) and the explicit companion values of
      Theorem 7.2 as ball identities: each difference is a ball containing 0 of radius
      below 2^-1900.
  (C) The Euler products (13)-(14), (71)-(73), (92), (93) as finite products with rigorous tail
      factors: for positive y_n, prod_{n>N} (1 + y_n) lies in [1, exp(sum_{n>N} y_n)],
      with sum_{n>N} n^-2 < 1/N and sum_{n>N} (n-1/2)^-2 < 1/(N-1/2); the finite
      splitting prod_{n<=2N} (1 + b^2/(pi^2 n^2)) = prod_{m<=N} (1 + a^2/(pi^2 m^2))
      prod_{m<=N} (1 + a^2/(pi^2 (m-1/2)^2)) as a ball identity.
  (D) The resolvent traces (74)-(84) and the companion traces as spectral series with
      two-sided integral tail bounds (decreasing summands), compared with the closed
      forms of Proposition 6.3, Corollary 6.4 and Theorem 7.2.
  (E) Remark 7.5: the eight printed decimals are correctly rounded (strict ball
      inclusion in the half-unit interval of the last printed digit), and the sums and
      products (91), (94)-(96) of the printed values agree with the printed values of
      Sections 2-6 within the rounding of the printed digits.

Every Arb quantity is a ball; comparisons are certified ball inequalities.
Requires python-flint 0.9.0.
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
    print(f"{'PASS' if ok else 'FAIL'} {count:02d}: {desc}")
    if not ok:
        failures.append(desc)


def qball(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


TINY = arb(2) ** (-1900)


def is_zero_ball(x):
    return x.contains(0) and abs(x).upper() < TINY


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, "
      f"Arb precision {ctx.prec} bits")

pi = arb.pi()
s2 = arb(2).sqrt()
s8 = arb(8).sqrt()
a = 1 / s8
b = 1 / s2


def coth(x):
    return x.cosh() / x.sinh()


def L(x):            # Langevin function coth x - 1/x
    return coth(x) - 1 / x


def V(x):            # Langevin variance 1/x^2 - 1/sinh^2 x
    return 1 / (x * x) - 1 / (x.sinh() ** 2)


def rE_imag(x):      # r_E(2 i x) = sinh(x)/x
    return x.sinh() / x


# ---------------------------------------------------------------- (A) Lemma 7.1
I = acb(0, 1)
z0 = I / acb(s2)
z1 = I * acb(s2)
check("(89) 2 z0^2 + 1 = 0 (complex ball)",
      (2 * z0 * z0 + 1).contains(0) and abs(2 * z0 * z0 + 1).upper() < TINY)
check("(89) S z0 = -1/z0 = z1 and z1 = 2 z0",
      (-1 / z0 - z1).contains(0) and (z1 - 2 * z0).contains(0))
check("(89) S z1 = -1/z1 = z0", (-1 / z1 - z0).contains(0))
check("(89) -z0 = -i/sqrt(2) is not in the upper half-plane: Im(-z0) < 0",
      (-z0).imag < 0)
check("a^2 = 1/8, b^2 = 1/2, b = 2a",
      is_zero_ball(a * a - qball(Q(1, 8))) and is_zero_ball(b * b - qball(Q(1, 2)))
      and is_zero_ball(b - 2 * a))
rz0 = rE_imag(a)
rz1 = rE_imag(b)
diff = rz1 - rz0
check("(90) r_E(z1) - r_E(z0) = (cosh a - 1) sinh(a)/a",
      is_zero_ball(diff - (a.cosh() - 1) * rz0))
check("(90) r_E(z1) - r_E(z0) > 0 (strict ball inequality)", diff > 0)

# ---------------------------------------------------------------- (B) exact identities
check("(91) r_E(z1) = cosh(1/sqrt 8) r_E(z0)", is_zero_ball(rz1 - (1 / s8).cosh() * rz0))
check("(94) 2 L(b) = L(a) + tanh(a)", is_zero_ball(2 * L(b) - L(a) - a.tanh()))
check("(95) 4 Var_b = Var_a + sech^2(a)", is_zero_ball(4 * V(b) - V(a) - 1 / a.cosh() ** 2))

TD_a = (coth(a) - s8) * s2                 # (77)
TDN_a = s2 * a.tanh()                       # (79)
TD_b = coth(b) / s2 - 1                     # Theorem 7.2, explicit value
QD_a = 2 * (2 * TD_a - V(a))                # (84)
QD_b = TD_b - V(b) / 2                      # (76) at x = b, 4 b^2 = 2
check("(74) at x = a: L(a) = 2a Tr(A + a^2)^-1 with (77)", is_zero_ball(L(a) - 2 * a * TD_a))
check("(75) at x = a: tanh(a) = 2a Tr(A_DN + a^2)^-1 with (79)",
      is_zero_ball(a.tanh() - 2 * a * TDN_a))
check("(96) 4 Tr(2/(2A+I)) = Tr(8/(8A+I)) + Tr(8/(8A_DN+I))",
      is_zero_ball(4 * TD_b - TD_a - TDN_a))
check("Theorem 7.2: L(b) = coth b - sqrt 2", is_zero_ball(L(b) - (coth(b) - s2)))
check("Theorem 7.2: Var_b = 2 - csch^2 b", is_zero_ball(V(b) - (2 - 1 / b.sinh() ** 2)))
check("Theorem 7.2: Tr(A + I/2)^-1 = coth(b)/sqrt 2 - 1 = L(b)/(2b)",
      is_zero_ball(TD_b - L(b) / (2 * b)))

# ---------------------------------------------------------------- (C) Euler products
N = 4000


def prod_dirichlet(x, N):
    p = arb(1)
    for n in range(1, N + 1):
        p *= 1 + x * x / (pi * pi * n * n)
    return p


def prod_dn(x, N):
    p = arb(1)
    for m in range(1, N + 1):
        h = arb(2 * m - 1) / 2
        p *= 1 + x * x / (pi * pi * h * h)
    return p


for name, x in (("a", a), ("b", b)):
    PN = prod_dirichlet(x, N)
    tail = (x * x / (pi * pi * N)).exp()
    check(f"(13), (71) sinh(x)/x = prod (1 + x^2/(pi^2 n^2)) at x = {name}: "
          f"P_N < sinh(x)/x < P_N exp(x^2/(pi^2 N)), N = {N}",
          PN < rE_imag(x) < PN * tail)
QN = prod_dn(a, N)
check(f"(14), (72) cosh(a) = prod (1 + a^2/(pi^2 (n-1/2)^2)): "
      f"Q_N < cosh(a) < Q_N exp(a^2/(pi^2 (N-1/2))), N = {N}",
      QN < a.cosh() < QN * (a * a / (pi * pi * (arb(N) - arb(1) / 2))).exp())
P2N_b = prod_dirichlet(b, 2 * N)
PN_a = prod_dirichlet(a, N)
check("(92) finite splitting: prod_{n<=2N}(1 + b^2/(pi^2 n^2)) = "
      "prod_{m<=N}(1 + a^2/(pi^2 m^2)) prod_{m<=N}(1 + a^2/(pi^2 (m-1/2)^2))",
      (P2N_b - PN_a * QN).contains(0) and abs(P2N_b - PN_a * QN).upper() < arb(2) ** (-1800))
check("(92) r_E(z1) = r_E(z0) cosh(a) = (sinh(b)/b)", is_zero_ball(rz1 - rz0 * a.cosh()))
P93 = arb(1)
for n in range(1, N + 1):
    P93 *= 1 + 1 / (2 * pi * pi * n * n)
check("(93) r_E(z1) = prod (1 + 1/(2 pi^2 n^2)) with tail factor exp(1/(2 pi^2 N))",
      P93 < rz1 < P93 * (1 / (2 * pi * pi * N)).exp())
P62 = arb(1)
for n in range(1, N + 1):
    P62 *= 1 + 1 / (8 * pi * pi * n * n)
check("(73) r_E(z0) = prod (1 + 1/(8 pi^2 n^2)) with tail factor exp(1/(8 pi^2 N))",
      P62 < rz0 < P62 * (1 / (8 * pi * pi * N)).exp())

# ---------------------------------------------------------------- (D) traces as series
M = 4000


def series_dirichlet(x, M):
    s = arb(0)
    for n in range(1, M + 1):
        s += 1 / (pi * pi * n * n + x * x)
    # sum_{n>M} f(n), f decreasing: int_{M+1}^oo f <= tail <= int_M^oo f,
    # int_c^oo dt/(pi^2 t^2 + x^2) = atan(x/(pi c))/(pi x)
    lo = (x / (pi * (M + 1))).atan() / (pi * x)
    hi = (x / (pi * M)).atan() / (pi * x)
    return s + lo, s + hi


def series_dn(x, M):
    s = arb(0)
    for m in range(1, M + 1):
        h = arb(2 * m - 1) / 2
        s += 1 / (pi * pi * h * h + x * x)
    # g(s) = 1/(pi^2 s^2 + x^2) decreasing, summed at s = m - 1/2, m > M:
    # int_{M+1/2}^oo g <= tail <= int_{M-1/2}^oo g
    lo = (x / (pi * (arb(M) + arb(1) / 2))).atan() / (pi * x)
    hi = (x / (pi * (arb(M) - arb(1) / 2))).atan() / (pi * x)
    return s + lo, s + hi


def series_square(x, M):
    s = arb(0)
    for n in range(1, M + 1):
        d = pi * pi * n * n + x * x
        s += 1 / (d * d)
    # 0 <= tail <= sum_{n>M} 1/(pi^4 n^4) <= 1/(3 pi^4 M^3)
    return s, s + 1 / (3 * pi ** 4 * arb(M) ** 3)


lo, hi = series_dirichlet(a, M)
check("(77), (81) Tr(8/(8A+I)) = sum 8/(8 pi^2 n^2 + 1) encloses sqrt2 [coth a - sqrt 8]",
      lo < TD_a < hi)
lo, hi = series_dn(a, M)
check("(79), (82) Tr(8/(8A_DN+I)) = sum 8/(8 pi^2 (n-1/2)^2 + 1) encloses sqrt2 tanh a",
      lo < TDN_a < hi)
lo, hi = series_square(a, M)
check("(83)-(84) Tr(64/(8A+I)^2) = sum 64/(8 pi^2 n^2 + 1)^2 encloses 2[2 Tr - L'(a)]",
      lo < QD_a < hi)
lo, hi = series_dirichlet(b, M)
check("Theorem 7.2: Tr(2/(2A+I)) = sum 2/(2 pi^2 n^2 + 1) encloses coth(b)/sqrt2 - 1",
      lo < TD_b < hi)
lo, hi = series_square(b, M)
check("Remark 7.5: Tr(4/(2A+I)^2) = sum 4/(2 pi^2 n^2 + 1)^2 encloses Tr - Var_b/2",
      lo < QD_b < hi)

# ---------------------------------------------------------------- (E) printed decimals
printed_companion = [
    ("r_E(z1) = sinh(b)/b", rz1, "1.0854416412726070018696230810771799943362362464373"),
    ("cosh(a)", a.cosh(), "1.0631537604037705983260079789718467840680879072616"),
    ("tanh(a)", a.tanh(), "0.33952309865331385123358989166828821555857242983167"),
    ("sech^2(a)", 1 / a.cosh() ** 2, "0.88472406548085211009890188842493156897779476147375"),
    ("L(b)", L(b), "0.22820184167862343547106085276503992978675557681550"),
    ("Var_b(omega_3)", V(b), "0.30247164053363031351513391306894250708230381630266"),
    ("Tr(2/(2A+I))", TD_b, "0.16136306973021354259596368552812207371730496161722"),
    ("Tr(4/(2A+I)^2)", QD_b, "0.010127249463398385838396728993650820176153053465894"),
]
printed_earlier = {
    "rE0": (rz0, "1.0209639298650195104786646351804211019462043266699"),
    "La": (L(a), "0.11688058470393301970853181386179164401493872379933"),
    "Va": (V(a), "0.32516249665366914396163376385083845935142050373689"),
    "TDa": (TD_a, "0.16529410806639939866550278088492457407260894951106"),
    "TDNa": (TDN_a, "0.48015817085445477171835196122756372079661089695783"),
}


def ulp(p):
    return Q(1, 10 ** len(p.split(".")[1]))


def correctly_rounded(val, p):
    h = ulp(p) / 2
    return qball(Q(p) - h) < val < qball(Q(p) + h)


for name, val, p in printed_companion:
    check(f"Remark 7.5: {name} correctly rounded to {len(p.split('.')[1])} decimals",
          correctly_rounded(val, p))
for key, (val, p) in printed_earlier.items():
    check(f"printed value {key} of Sections 2-6 correctly rounded", correctly_rounded(val, p))

P = {name: Q(p) for name, _, p in printed_companion}
E = {key: Q(p) for key, (_, p) in printed_earlier.items()}
U = {name: ulp(p) for name, _, p in printed_companion}
UE = {key: ulp(p) for key, (_, p) in printed_earlier.items()}
# (91): |p1 - pc p0| <= u1/2 + (pc u0 + p0 uc)/2 + uc u0/4
bound91 = U["r_E(z1) = sinh(b)/b"] / 2 + (P["cosh(a)"] * UE["rE0"] + E["rE0"] * U["cosh(a)"]) / 2 \
    + U["cosh(a)"] * UE["rE0"] / 4
check("(91) printed r_E(z1) agrees with printed cosh(a) x printed r_E(z0) within rounding",
      abs(P["r_E(z1) = sinh(b)/b"] - P["cosh(a)"] * E["rE0"]) <= bound91)
check("(94) printed 2 L(b) = printed L(a) + tanh(a) within rounding",
      abs(2 * P["L(b)"] - E["La"] - P["tanh(a)"]) <= U["L(b)"] + UE["La"] / 2 + U["tanh(a)"] / 2)
check("(95) printed 4 Var_b = printed Var_a + sech^2(a) within rounding",
      abs(4 * P["Var_b(omega_3)"] - E["Va"] - P["sech^2(a)"])
      <= 2 * U["Var_b(omega_3)"] + UE["Va"] / 2 + U["sech^2(a)"] / 2)
check("(96) printed 4 Tr(2/(2A+I)) = printed (78) + printed (80) within rounding",
      abs(4 * P["Tr(2/(2A+I))"] - E["TDa"] - E["TDNa"])
      <= 2 * U["Tr(2/(2A+I))"] + UE["TDa"] / 2 + UE["TDNa"] / 2)

print("r_E(z1)        =", rz1.str(60, radius=False))
print("cosh(a)        =", a.cosh().str(60, radius=False))
print("Tr(2/(2A+I))   =", TD_b.str(60, radius=False))
print("Tr(4/(2A+I)^2) =", QD_b.str(60, radius=False))
if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    sys.exit(1)
print(f"ALL {count} SECTION 6/7 DUPLICATION CHECKS PASSED (precision {ctx.prec} bits)")
