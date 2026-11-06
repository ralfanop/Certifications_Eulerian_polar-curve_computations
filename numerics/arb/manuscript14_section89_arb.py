#!/usr/bin/env python3
"""Manuscript 14, Sections 8 and 9: Arb certificate at 2000 bits.

Notation: a = 1/sqrt(8), b = 1/sqrt(2) = |z0|, z0 = i b, z1 = i sqrt(2), Q(tau) = tau^2/2,
E(q) = prod_n (1 - q/(2 pi^2 n^2)), r_E(tau) = sin(tau/2)/(tau/2), K_sd = log(1 + sqrt 2)/2,
mu_hex = sqrt(2 + sqrt 2).

  (A) Theorem 8.1: the fibre Q^{-1}(-1/4) = {z0, -z0}, the actions (111) of S and of the
      dilation, S z0 = 2 z0 and S(1/sqrt2) = -2/sqrt2; the factorisation r_E = E o Q at the
      special point and at a complex sample point, with a rigorous tail bound for the
      product; the evenness of r_E; m(-H) = 1 - m(H); the monodromy (109) of the lifts.
  (B) Proposition 8.2: C0 of (112) and its printed decimals (113); the four forms of (114)
      as ball identities; the resolvent traces as spectral series with two-sided tail
      bounds; the logarithmic derivatives of (ii); the Bernoulli series (115) in exact
      rationals with a geometric tail, its five displayed terms, its zeta form; the
      companion identity (116) and the printed decimals (117).
  (C) Proposition 8.4: K_sd and its printed decimals (119); (121)-(123) as ball identities;
      the boundary value G(-1/4) = 1/sqrt2 by an exact alternating bracket and by the
      arcsine-law integral; Z* = (sqrt2 - 1)/2 and 4Z*^2 + 4Z* - 1 = 0; arctan z0 = 2i K_sd;
      the arcsine moments; Remark 8.5: lambda = (1 + sqrt2)^4 = 17 + 12 sqrt2 = e^{8 K_sd}.
  (D) Proposition 8.6: a_n = 2cos(pi/2^{n+1}) and T_2(a_{n+1}/2) = a_n/2 for n <= 30,
      T_2(mu/2) = |z0|, T_4(mu/2) = 0; the characteristic polynomials of the paths P_m,
      m <= 12, computed exactly (Faddeev-LeVerrier) and compared with U_m(lambda/2); the
      factorisation (124) and the spectrum of P7; Viete's product (125) with a rigorous tail;
      the integral (126).
  (E) Proposition 8.7: closed walks on Z^2 counted by dynamic programming, length <= 24;
      the identities of the proof in exact integers, n <= 60; R_00(1/8) by its series with
      a geometric tail against 2F1(1/2,1/2;1;1/4) = 1/AGM(1, sqrt3/2) with an AGM bracket.
  (F) Section 9: Lemma 9.2 and Theorem 9.3 on exact Gaussian-rational spinors; the
      pushforward (131) through the averages (132)-(133) as integrals; Proposition 9.5:
      (135)-(138), the derivative identity, the sublevel sums (134) of B_J for J = 1/2, 1,
      3/2, 7/2, the spectral forms of cosh x and tanh x with rigorous tails; Proposition 9.7 (iv).

Every Arb quantity is a ball; comparisons are certified ball inequalities.
Requires python-flint 0.9.0.
"""
from fractions import Fraction as Q
from math import comb, factorial
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


def ulp(p):
    return Q(1, 10 ** len(p.split('.')[1]))


def correctly_rounded(val, p):
    h = ulp(p) / 2
    return qball(Q(p) - h) < val < qball(Q(p) + h)


def in_bracket(val, lo, hi):
    return lo <= val and val <= hi


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, "
      f"Arb precision {ctx.prec} bits")

pi = arb.pi()
s2 = arb(2).sqrt()
a = 1 / arb(8).sqrt()
b = 1 / s2
I = acb(0, 1)
z0 = acb(0, b)
z1 = acb(0, s2)


def coth(x):
    return x.cosh() / x.sinh()


def L(x):
    return coth(x) - 1 / x


def Lp(x):
    return 1 / (x * x) - 1 / (x.sinh() ** 2)


def Qmap(t):
    return t * t / 2


def S(t):
    return -1 / t


def rE(t):
    return (t / 2).sin() / (t / 2)


# ---------------------------------------------------------------- (A) Theorem 8.1
print("--- (A) Theorem 8.1")
check("(A) Q(z0) = -1/4 and Q(-z0) = -1/4", is_zero_ball(Qmap(z0) + qball(Q(1, 4)))
      and is_zero_ball(Qmap(-z0) + qball(Q(1, 4))))
check("(A) 2 z0^2 + 1 = 0 (the equation of Lemma 7.1)", is_zero_ball(2 * z0 * z0 + 1))
samples = [acb(qball(Q(3, 10)), qball(Q(7, 10))), acb(qball(Q(-13, 10)), qball(Q(2, 5))),
           acb(qball(Q(1, 7)), qball(Q(-9, 4))), z0, z1]
check("(A) (111): Q(S tau) = 1/(4 Q(tau)) at five points",
      all(is_zero_ball(Qmap(S(t)) - 1 / (4 * Qmap(t))) for t in samples))
check("(A) (111): Q(2 tau) = 4 Q(tau) at five points",
      all(is_zero_ball(Qmap(2 * t) - 4 * Qmap(t)) for t in samples))
check("(A) over q = -1/4: S z0 = 2 z0", is_zero_ball(S(z0) - 2 * z0))
check("(A) over q = 1/4: Q(1/sqrt2) = 1/4 and S(1/sqrt2) = -2/sqrt2 = delta(2/sqrt2)",
      is_zero_ball(Qmap(b) - qball(Q(1, 4))) and is_zero_ball(S(b) + 2 * b))
check("(A) z0 is in H and -z0 is not", z0.imag > 0 and (-z0).imag < 0)
check("(A) |Q(tau)| = |tau|^2/2 on the circle |tau| = 1/sqrt2 (points e^{i k pi/7}/sqrt2)",
      all(is_zero_ball(abs(Qmap(b * (I * pi * k / 7).exp())) - qball(Q(1, 4))) for k in range(14)))
# r_E(z0) = E(-1/4) = sinh(a)/a, product with rigorous tail
N = 4000
P = arb(1)
for n in range(1, N + 1):
    P *= 1 + 1 / (8 * pi ** 2 * n * n)
target = a.sinh() / a
check("(A) r_E(z0) = sin(z0/2)/(z0/2) = sinh(a)/a", is_zero_ball(rE(z0) - target))
check(f"(A) E(-1/4) = prod (1 + 1/(8 pi^2 n^2)) in [P_N, P_N exp(1/(8 pi^2 N))], N = {N}, "
      "contains sinh(a)/a", in_bracket(target, P, P * (1 / (8 * pi ** 2 * N)).exp()))
# r_E = E o Q at complex points, |r_E - P_N| <= |P_N| (exp(t) - 1), t = |tau|^2/(4 pi^2 N)
ok = True
for t in samples[:3]:
    PN = acb(1)
    for n in range(1, 1001):
        PN *= 1 - Qmap(t) / (2 * pi ** 2 * n * n)
    tail = (abs(t) ** 2 / (4 * pi ** 2 * 1000)).exp() - 1
    ok = ok and abs(rE(t) - PN) <= abs(PN) * tail
check("(A) (108): r_E(tau) = E(Q(tau)) at three complex points, rigorous tail bound", ok)
check("(A) (108): r_E(-tau) = r_E(tau) at five points",
      all(is_zero_ball(rE(-t) - rE(t)) for t in samples))
Hs = [qball(Q(1, 3)), arb(1), qball(Q(5, 2)), b, s2]
check("(A) field axis: r_E(-iH) = sinh(H/2)/(H/2), even in H",
      all(is_zero_ball(rE(acb(0, -H)) - (H / 2).sinh() / (H / 2))
          and is_zero_ball(rE(acb(0, H)) - rE(acb(0, -H))) for H in Hs))
check("(A) m(-H) = 1 - m(H) with m(H) = [1 + L(H/2)]/2",
      all(is_zero_ball((1 + L(-H / 2)) / 2 - (1 - (1 + L(H / 2)) / 2)) for H in Hs))
ok = True
q0 = acb(qball(Q(-1, 4)), qball(Q(1, 9)))
for k in range(-4, 5):
    h0 = q0.log()
    h1 = h0 + 2 * pi * I * k
    lift0 = s2 * (h0 / 2).exp()
    lift1 = s2 * (h1 / 2).exp()
    ok = ok and is_zero_ball(Qmap(lift1) - q0) and is_zero_ball(lift1 - (1 if k % 2 == 0 else -1) * lift0)
check("(A) (109): lifts sqrt2 e^{h/2} of loops of winding k, -4 <= k <= 4, end at (-1)^k "
      "times the start and lie over the loop", ok)
check("(A) wn(Q o gamma) = 2 wn(gamma): Q(e^{g}) = e^{2g - log 2} at three points",
      all(is_zero_ball(Qmap(t.exp()) - (2 * t - arb(2).log()).exp()) for t in samples[:3]))

# ---------------------------------------------------------------- (B) Proposition 8.2
print("--- (B) Proposition 8.2")
C0 = qball(Q(3, 2)) - b * (b.cos() / b.sin())
p112 = "0.67250070367941164573437979080329518859340302862626"
check("(B) (113): C0 correctly rounded to 50 decimals", correctly_rounded(C0, p112))
check("(B) (114): 3/2 - z0 coth z0 = C0", is_zero_ball(qball(Q(3, 2)) - z0 * z0.cosh() / z0.sinh() - C0))
check("(B) (114): 1/2 - z0 L(z0) = C0",
      is_zero_ball(qball(Q(1, 2)) - z0 * (z0.cosh() / z0.sinh() - 1 / z0) - C0))
check("(B) (114): the value is unchanged at -z0",
      is_zero_ball(qball(Q(3, 2)) - (-z0) * (-z0).cosh() / (-z0).sinh() - C0))


def trace_bracket(shift, N, half=False):
    """Bracket of sum_{n>=1} 1/(pi^2 nu_n^2 - shift), nu_n = n or n - 1/2, shift > 0 small."""
    part = arb(0)
    s_inv = arb(0)
    for n in range(1, N + 1):
        nu = qball(Q(2 * n - 1, 2)) if half else arb(n)
        part += 1 / (pi ** 2 * nu ** 2 - shift)
        s_inv += 1 / (nu ** 2)
    total_inv = pi ** 2 / 2 if half else pi ** 2 / 6
    lo_tail = (total_inv - s_inv) / pi ** 2
    nuN = qball(Q(2 * N - 1, 2)) if half else arb(N)
    hi_tail = lo_tail + 2 * shift / (3 * pi ** 4 * nuN ** 3)
    return part + lo_tail, part + hi_tail


N = 3000
lo, hi = trace_bracket(qball(Q(1, 2)), N)
check(f"(B) (114): C0 in 1/2 + Tr((A - I/2)^-1) bracket, N = {N} (Tr(2/(2A - I)) is the same trace)",
      in_bracket(C0, qball(Q(1, 2)) + lo, qball(Q(1, 2)) + hi))
check("(B) A - I/2 positive: pi^2 - 1/2 > 0", pi ** 2 - qball(Q(1, 2)) > 0)
# (ii): logarithmic derivatives
th = s2
rEr = (th / 2).sin() / (th / 2)
drE = ((th / 2).cos() / 2 * (th / 2) - (th / 2).sin() / 2) / (th / 2) ** 2
check("(B) (ii): C0 = 1/2 - sqrt2 r_E'(sqrt2)/r_E(sqrt2)", is_zero_ball(qball(Q(1, 2)) - th * drE / rEr - C0))
sb = b  # s = sqrt(q/2) at q = 1
dlogE = (sb.cos() / sb.sin() - 1 / sb) / (4 * sb)
check("(B) (ii): C0 = 1/2 - 2 E'(1)/E(1), E(q) = sin(sqrt(q/2))/sqrt(q/2) for q > 0",
      is_zero_ball(qball(Q(1, 2)) - 2 * dlogE - C0))
check("(B) (ii): Q^{-1}(1) = {sqrt2, -sqrt2}, |sqrt2| = |z1|",
      is_zero_ball(Qmap(s2) - 1) and is_zero_ball(abs(z1) - s2))
# (iii): Bernoulli numbers
MB = 60
B = [Q(1)]
for n in range(1, 2 * MB + 1):
    B.append(-sum(comb(n + 1, k) * B[k] for k in range(n)) / (n + 1))
terms = [(-1) ** (m + 1) * 2 ** m * B[2 * m] / factorial(2 * m) for m in range(1, MB + 1)]
check("(B) (115): the first five Bernoulli terms are 1/6, 1/180, 1/3780, 1/75600, 1/1496880",
      terms[:5] == [Q(1, 6), Q(1, 180), Q(1, 3780), Q(1, 75600), Q(1, 1496880)])
check(f"(B) (115): all terms m <= {MB} positive (sign of B_2m is (-1)^(m+1))", all(t > 0 for t in terms))
partial = qball(Q(1, 2) + sum(terms))
r = 1 / (2 * pi ** 2)
tailB = 2 * 2 * r ** (MB + 1) / (1 - r)
check(f"(B) (115): C0 in [1/2 + S_{MB}, 1/2 + S_{MB} + 4 r^{MB+1}/(1-r)], r = 1/(2 pi^2)",
      in_bracket(C0, partial, partial + tailB))
ok = True
NZ = 2000
for m in range(1, 7):
    zl = sum(qball(Q(1, n ** (2 * m))) for n in range(1, NZ + 1))
    zh = zl + qball(Q(1, (2 * m - 1) * NZ ** (2 * m - 1)))
    zt = qball(terms[m - 1]) * 2 ** (m - 1) * pi ** (2 * m)
    ok = ok and in_bracket(zt, zl, zh)
check("(B) (115): zeta form, 2^{m-1} pi^{2m} x (Bernoulli term) lies in the bracket of zeta(2m), m <= 6", ok)
# (iv): companion
TDN = b * b.tan()
check("(B) (116): Tr((A_DN - I/2)^-1) = -z0 tanh z0 = tan(1/sqrt2)/sqrt2",
      is_zero_ball(-z0 * z0.tanh() - TDN))
lo, hi = trace_bracket(qball(Q(1, 2)), N, half=True)
check(f"(B) (116): tan(b)/sqrt2 in the spectral bracket of Tr((A_DN - I/2)^-1), N = {N}",
      in_bracket(TDN, lo, hi))
comp = qball(Q(3, 2)) - s2 * (s2.cos() / s2.sin())
check("(B) (116): C0 + Tr(2/(2A_DN - I)) = 3/2 - sqrt2 cot sqrt2", is_zero_ball(C0 + TDN - comp))
check("(B) (116): 3/2 - z1 coth z1 = 3/2 - sqrt2 cot sqrt2",
      is_zero_ball(qball(Q(3, 2)) - z1 * z1.cosh() / z1.sinh() - comp))
lo, hi = trace_bracket(arb(2), N)
check(f"(B) (116): 1/2 + Tr(2/(2A_2 - I)) = 1/2 + 4 Tr((A - 2I)^-1) in the spectral bracket, N = {N}",
      in_bracket(comp, qball(Q(1, 2)) + 4 * lo, qball(Q(1, 2)) + 4 * hi))
check("(B) least eigenvalue pi^2/4 of A_2 exceeds 1/2 and pi^2 exceeds 2",
      pi ** 2 / 4 > qball(Q(1, 2)) and pi ** 2 > 2)
p116 = "1.27673082474804740671137717691544684163532597865042"
check("(B) (117): companion value correctly rounded to 50 decimals", correctly_rounded(comp, p116))

# ---------------------------------------------------------------- (C) Proposition 8.4
print("--- (C) Proposition 8.4")
K = (1 + s2).log() / 2
p118 = "0.44068679350977151261630466248989615451408016413082"
check("(C) (119): K_sd correctly rounded to 50 decimals", correctly_rounded(K, p118))
check("(C) (118): sinh 2K_sd = 1", is_zero_ball((2 * K).sinh() - 1))
check("(C) (121): tanh 2K_sd = |z0| = b", is_zero_ball((2 * K).tanh() - b) and is_zero_ball(abs(z0) - b))
check("(C) (121): cosh 2K_sd = |z1| = 1/b", is_zero_ball((2 * K).cosh() - 1 / b) and is_zero_ball(abs(z1) - 1 / b))
Zs = (s2 - 1) / 2
check("(C) (122): tanh K_sd = e^{-2K_sd} = sqrt2 - 1 = 2 Z*",
      is_zero_ball(K.tanh() - (s2 - 1)) and is_zero_ball((-2 * K).exp() - (s2 - 1)) and is_zero_ball(2 * Zs - (s2 - 1)))
check("(C) 4 Z*^2 + 4 Z* - 1 = 0", is_zero_ball(4 * Zs ** 2 + 4 * Zs - 1))
t = K.tanh()
check("(C) sinh 2K = 2t/(1 - t^2) = 1 at t = tanh K_sd", is_zero_ball(2 * t / (1 - t * t) - 1))
check("(C) Kramers-Wannier: sinh 2K sinh 2K* = 1 with tanh K* = e^{-2K}, at K = 1/3",
      is_zero_ball((qball(Q(2, 3))).sinh() * (2 * ((qball(Q(-2, 3))).exp()).atanh()).sinh() - 1))
check("(C) (123): arctan z0 = 2 i K_sd", is_zero_ball(z0.atan() - acb(0, 2 * K)))
check("(C) (123): H0 = -1/sqrt2 = -tanh 2K_sd and H1 = -sqrt2 = -coth 2K_sd",
      is_zero_ball(-b + (2 * K).tanh()) and is_zero_ball(-s2 + coth(2 * K)))
# (120): G(-1/4) by exact alternating partial sums
KG = 3000
c = [Q(comb(2 * k, k), 4 ** k) for k in range(KG + 2)]
check(f"(C) (120): |C(2k,k)(-1/4)^k| strictly decreasing for k <= {KG + 1}",
      all(c[k + 1] < c[k] for k in range(KG + 1)))
SK = sum((-1) ** k * c[k] for k in range(KG + 1))
SK1 = SK + (-1) ** (KG + 1) * c[KG + 1]
check(f"(C) (120): 1/sqrt2 lies between the partial sums S_{KG} and S_{KG + 1} of G(-1/4)",
      in_bracket(b, qball(min(SK, SK1)), qball(max(SK, SK1))))
Gint = acb.integral(lambda x, analytic: 1 / (1 + x.sin() ** 2), acb(0), acb(pi)) / pi
check("(C) (120): (1/pi) int_0^pi d theta/(1 + sin^2 theta) = 1/sqrt2", is_zero_ball(Gint - b))
check("(C) (120): Z* = G(-1/4) - 1 + 1/2 = (sqrt2 - 1)/2", is_zero_ball(b - 1 + qball(Q(1, 2)) - Zs))
check("(C) (120): z0 = i G(Q(z0)) = i/sqrt(1 - 4 Q(z0))",
      is_zero_ball(z0 - I / (1 - 4 * Qmap(z0)).sqrt()))
ok = True
for n in range(1, 6):
    mom = acb.integral(lambda x, analytic, n=n: x.sin() ** (2 * n), acb(0), acb(pi)) / pi
    ok = ok and is_zero_ball(mom - qball(Q(comb(2 * n, n), 4 ** n)))
check("(C) arcsine moments (1/pi) int_0^pi sin^{2n} = C(2n,n)/4^n, n <= 5", ok)
check("(C) cyclohedron counts C(2k,k), k = 2..6: 6, 20, 70, 252, 924",
      [comb(2 * k, k) for k in range(2, 7)] == [6, 20, 70, 252, 924])
lam = (1 + s2) ** 4
check("(C) Remark 8.5: lambda = (1 + sqrt2)^4 = 17 + 12 sqrt2 = e^{8 K_sd}",
      is_zero_ball(lam - 17 - 12 * s2) and is_zero_ball((8 * K).exp() - lam))
check("(C) Remark 8.5: (1/2) log(sqrt2 - 1) = -K_sd and (sqrt2 - 1)^4 = 1/lambda",
      is_zero_ball((s2 - 1).log() / 2 + K) and is_zero_ball((s2 - 1) ** 4 * lam - 1))

# ---------------------------------------------------------------- (D) Proposition 8.6
print("--- (D) Proposition 8.6")
mu = (2 + s2).sqrt()
an = [arb(0)]
for n in range(31):
    an.append((2 + an[-1]).sqrt())
check("(D) a_1 = sqrt2, a_2 = mu_hex", is_zero_ball(an[1] - s2) and is_zero_ball(an[2] - mu))
check("(D) (i): a_n = 2 cos(pi/2^{n+1}), n <= 30",
      all(is_zero_ball(an[n] - 2 * (pi / 2 ** (n + 1)).cos()) for n in range(31)))


def T2(y):
    return 2 * y * y - 1


def T4(y):
    return 8 * y ** 4 - 8 * y * y + 1


check("(D) (i): T_2(a_{n+1}/2) = a_n/2, n <= 29", all(is_zero_ball(T2(an[n + 1] / 2) - an[n] / 2) for n in range(30)))
check("(D) (i): T_2(mu/2) = |z0|, T_4(mu/2) = 0, T_4 = T_2 o T_2 at mu/2",
      is_zero_ball(T2(mu / 2) - b) and is_zero_ball(T4(mu / 2)) and is_zero_ball(T4(mu / 2) - T2(T2(mu / 2))))
check("(D) (i): mu^4 - 4 mu^2 + 2 = 0", is_zero_ball(mu ** 4 - 4 * mu ** 2 + 2))


def poly_mul(p, q):
    r_ = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r_[i + j] += x * y
    return r_


def charpoly(M):
    n = len(M)
    coeffs = [Q(0)] * (n + 1)
    coeffs[n] = Q(1)
    Mk = [[Q(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        AM = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        Mk = [[AM[i][j] + (coeffs[n - k + 1] if i == j else 0) for j in range(n)] for i in range(n)]
        AMk = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        coeffs[n - k] = -sum(AMk[i][i] for i in range(n)) / k
    return coeffs  # coefficient list, index = power of lambda


def U_lambda_half(m):
    """Coefficients (in lambda) of U_m(lambda/2): p_{-1} = 0, p_0 = 1, p_{k+1} = lambda p_k - p_{k-1}."""
    p_prev, p = [Q(0)], [Q(1)]
    for _ in range(m):
        nxt = [Q(0)] + p
        for i, x in enumerate(p_prev):
            nxt[i] -= x
        p_prev, p = p, nxt
    return p


ok = True
for m in range(1, 13):
    A_ = [[Q(1) if abs(i - j) == 1 else Q(0) for j in range(m)] for i in range(m)]
    cp = charpoly(A_)
    ok = ok and cp == U_lambda_half(m)
check("(D) (ii): det(lambda I - A_{P_m}) = U_m(lambda/2) exactly, m <= 12 (Faddeev-LeVerrier)", ok)
# U_m via the Chebyshev recurrence in x and substitution x = lambda/2
ok = True
Ux = [[Q(1)], [Q(0), Q(2)]]
for n in range(1, 12):
    nxt = [Q(0)] + [2 * x for x in Ux[n]]
    for i, x in enumerate(Ux[n - 1]):
        nxt[i] -= x
    Ux.append(nxt)
for m in range(1, 13):
    sub = [x / 2 ** i for i, x in enumerate(Ux[m])]
    ok = ok and sub == U_lambda_half(m)
check("(D) (ii): U_{n+1} = 2x U_n - U_{n-1} at x = lambda/2 gives the same polynomials, m <= 12", ok)
f123 = poly_mul(poly_mul([Q(0), Q(1)], [Q(-2), Q(0), Q(1)]), [Q(2), Q(0), Q(-4), Q(0), Q(1)])
check("(D) (124): U_7(lambda/2) = lambda (lambda^2 - 2)(lambda^4 - 4 lambda^2 + 2) exactly",
      f123 == U_lambda_half(7))


def evalp(p, x):
    acc = arb(0)
    for cc in reversed(p):
        acc = acc * x + qball(cc)
    return acc


eig = [2 * (j * pi / 8).cos() for j in range(1, 8)]
check("(D) (ii): the seven eigenvalues 2cos(j pi/8) are zeros of U_7(lambda/2)",
      all(is_zero_ball(evalp(f123, e)) for e in eig))
check("(D) (ii): eigenvectors sin(j k pi/8): A_{P7} v_j = 2cos(j pi/8) v_j, j = 1..7",
      all(all(is_zero_ball((((k - 1) * j * pi / 8).sin() if k > 1 else arb(0))
                           + (((k + 1) * j * pi / 8).sin() if k < 7 else arb(0))
                           - eig[j - 1] * (k * j * pi / 8).sin()) for k in range(1, 8)) for j in range(1, 8)))
check("(D) (ii): the boundary terms vanish: sin(8 j pi/8) = 0", all(is_zero_ball((j * pi).sin()) for j in range(1, 8)))
check("(D) (ii): Perron eigenvalue 2cos(pi/8) = mu_hex is the largest; +-sqrt2 = +-|z1| in the spectrum",
      is_zero_ball(eig[0] - mu) and all(eig[0] > e for e in eig[1:])
      and is_zero_ball(eig[1] - s2) and is_zero_ball(eig[5] + s2))
check("(D) (ii): eigenvalues distinct", all(eig[j] > eig[j + 1] for j in range(6)))
# (iii): Viete
NV = 200
prod = arb(1)
for n in range(1, NV + 1):
    prod *= an[n] / 2 if n <= 30 else (pi / 2 ** (n + 1)).cos()
xN = pi / 2 ** (NV + 1)
check(f"(D) (iii): prod_{{n<=N}} a_n/2 = 1/(2^N sin(pi/2^(N+1))), N = {NV}",
      is_zero_ball(prod - 1 / (2 ** NV * xN.sin())))
check("(D) (iii): 2/pi <= prod_{n<=N} a_n/2 <= (2/pi)/(1 - x_N^2/6), x_N = pi/2^(N+1)",
      in_bracket(prod, 2 / pi, (2 / pi) / (1 - xN ** 2 / 6)))
check("(D) (iii): r_E(pi) = 2/pi; the first two factors are |z0| and mu_hex/2",
      is_zero_ball(rE(pi) - 2 / pi) and is_zero_ball(an[1] / 2 - b) and is_zero_ball(an[2] / 2 - mu / 2))
check("(D) (iii): cosh(i pi/2^{k+1}) = cos(pi/2^{k+1}) = a_k/2, k <= 10",
      all(is_zero_ball(acb(0, pi / 2 ** (k + 1)).cosh() - an[k] / 2) for k in range(1, 11)))
# (iv): the integral (126)
kappa = pi / arb(8).sqrt()
I4 = 2 * acb.integral(lambda x, analytic: x.cos() ** 6 / (x.cos() ** 8 + x.sin() ** 8), acb(0), acb(pi / 2))
check("(D) (126): int dt/(1 + t^8) = 2 int_0^{pi/2} cos^6/(cos^8 + sin^8) = kappa mu_hex", is_zero_ball(I4 - kappa * mu))
check("(D) (126): (pi/4)/sin(pi/8) = (pi/sqrt8) sqrt(2 + sqrt2)", is_zero_ball((pi / 4) / (pi / 8).sin() - kappa * mu))
check("(D) (126): 2 sin(pi/8) = sqrt(2 - sqrt2) and sqrt(2 - sqrt2) sqrt(2 + sqrt2) = sqrt2",
      is_zero_ball(2 * (pi / 8).sin() - (2 - s2).sqrt()) and is_zero_ball((2 - s2).sqrt() * mu - s2))

# ---------------------------------------------------------------- (E) Proposition 8.7
print("--- (E) Proposition 8.7")
NW = 24
R = NW
grid = {(0, 0): 1}
counts = [1]
for step in range(1, NW + 1):
    new = {}
    for (x, y), v in grid.items():
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            key = (x + dx, y + dy)
            new[key] = new.get(key, 0) + v
    grid = new
    counts.append(grid.get((0, 0), 0))
check(f"(E) (127): closed walks of length 2n on Z^2 equal C(2n,n)^2, 2n <= {NW}",
      all(counts[2 * n] == comb(2 * n, n) ** 2 for n in range(NW // 2 + 1)))
check(f"(E) (127): closed walks of odd length vanish, length <= {NW}", all(counts[2 * n + 1] == 0 for n in range(NW // 2)))
check("(E) sum_j (2n)!/(j!^2 (n-j)!^2) = C(2n,n) sum_j C(n,j)^2 = C(2n,n)^2, n <= 60",
      all(sum(Q(factorial(2 * n), factorial(j) ** 2 * factorial(n - j) ** 2) for j in range(n + 1)) == comb(2 * n, n) ** 2
          and sum(comb(n, j) ** 2 for j in range(n + 1)) == comb(2 * n, n) for n in range(61)))
check("(E) 16^n (C(2n,n)/4^n)^2 = C(2n,n)^2 (moment form), n <= 60",
      all(16 ** n * Q(comb(2 * n, n), 4 ** n) ** 2 == comb(2 * n, n) ** 2 for n in range(61)))


def poch_half(n):
    p = Q(1)
    for i in range(n):
        p *= Q(1, 2) + i
    return p


check("(E) (1/2)_n = (2n)!/(4^n n!) and (1/2)_n^2 16^n/n!^2 = C(2n,n)^2, n <= 60",
      all(poch_half(n) == Q(factorial(2 * n), 4 ** n * factorial(n))
          and poch_half(n) ** 2 * 16 ** n / factorial(n) ** 2 == comb(2 * n, n) ** 2 for n in range(61)))
zq = Q(1, 8)
MS = 1500
Rs = qball(sum(comb(2 * n, n) ** 2 * zq ** (2 * n) for n in range(MS + 1)))
Rtail = qball(Q(4, 3) * Q(1, 4) ** (MS + 1))
x0, y0 = arb(1), arb(3).sqrt() / 2
for _ in range(14):
    x0, y0 = (x0 + y0) / 2, (x0 * y0).sqrt()
check("(E) AGM(1, sqrt3/2) lies between g_n and a_n, and a_n - g_n < 2^-1900 after 14 steps",
      abs(x0 - y0).upper() < TINY)
Ragm = 1 / x0.union(y0)
check(f"(E) (128)-(129): R_00(1/8) = sum C(2n,n)^2/64^n (n <= {MS}, tail <= (4/3) 4^-{MS + 1}) "
      "agrees within 2^-1900 with 2F1(1/2,1/2;1;1/4) = 1/AGM(1, sqrt3/2)",
      Rtail < TINY and abs(Ragm - Rs).upper() < TINY)

# ---------------------------------------------------------------- (F) Section 9
print("--- (F) Section 9")


def conj(z):
    return z.conjugate()


def Theta(psi):
    return (-conj(psi[1]), conj(psi[0]))


def herm(phi, psi):
    return conj(phi[0]) * psi[0] + conj(phi[1]) * psi[1]


sig = [((acb(0), acb(1)), (acb(1), acb(0))),
       ((acb(0), acb(0, -1)), (acb(0, 1), acb(0))),
       ((acb(1), acb(0)), (acb(0), acb(-1)))]


def apply(M, psi):
    return (M[0][0] * psi[0] + M[0][1] * psi[1], M[1][0] * psi[0] + M[1][1] * psi[1])


def bloch(psi):
    nrm = herm(psi, psi).real
    return [herm(psi, apply(s_, psi)).real / nrm for s_ in sig]


def g(p, q):
    return acb(qball(p), qball(q))


spinors = [(g(1, 0), g(0, 0)), (g(0, 0), g(1, 0)), (g(3, 1), g(-2, 5)), (g(Q(1, 3), -2), g(Q(7, 5), Q(1, 2))),
           (g(-4, 0), g(0, 9)), (g(Q(2, 7), Q(-5, 3)), g(-1, -1))]
check("(F) Lemma 9.2: Theta^2 = -I on six spinors",
      all(all(is_zero_ball(x + y) for x, y in zip(Theta(Theta(p)), p)) for p in spinors))
check("(F) Lemma 9.2: <Theta phi, Theta psi> = conj <phi, psi> (antiunitary) on all pairs",
      all(is_zero_ball(herm(Theta(p), Theta(q)) - conj(herm(p, q))) for p in spinors for q in spinors))
lam_c = g(Q(2, 3), Q(-7, 4))
check("(F) Lemma 9.2: Theta(c psi + phi) = conj(c) Theta psi + Theta phi (antilinear)",
      all(all(is_zero_ball(x - (conj(lam_c) * y + z_))
              for x, y, z_ in zip(Theta((lam_c * p[0] + q[0], lam_c * p[1] + q[1])), Theta(p), Theta(q)))
          for p in spinors for q in spinors))
check("(F) Lemma 9.2: psi^dagger Theta psi = 0", all(is_zero_ball(herm(p, Theta(p))) for p in spinors))
check("(F) Lemma 9.2: Theta sigma_j = -sigma_j Theta, j = 1, 2, 3",
      all(all(is_zero_ball(x + y) for x, y in zip(Theta(apply(s_, p)), apply(s_, Theta(p))))
          for s_ in sig for p in spinors))
check("(F) Lemma 9.2: affine coordinate of Theta psi is -1/conj(zeta)",
      all(is_zero_ball(Theta(p)[1] / Theta(p)[0] + 1 / conj(p[1] / p[0]))
          for p in spinors if not p[0].is_zero() and not p[1].is_zero()))
check("(F) Lemma 9.2: Theta exchanges zeta = 0 and zeta = infinity",
      Theta(spinors[0])[0].is_zero() and Theta(spinors[1])[1].is_zero())
check("(F) Pauli algebra: sigma_j^2 = I, sigma_1 sigma_2 = i sigma_3, traceless, Hermitian",
      all(all(is_zero_ball(x - y) for x, y in zip(apply(s_, apply(s_, p)), p)) for s_ in sig for p in spinors)
      and all(all(is_zero_ball(x - I * y) for x, y in zip(apply(sig[0], apply(sig[1], p)), apply(sig[2], p))) for p in spinors)
      and all(is_zero_ball(s_[0][0] + s_[1][1]) and is_zero_ball(s_[0][1] - conj(s_[1][0])) for s_ in sig))
check("(F) Theorem 9.3 (131): omega_B(Theta psi) = -omega_B(psi)",
      all(all(is_zero_ball(x + y) for x, y in zip(bloch(Theta(p)), bloch(p))) for p in spinors))
check("(F) Theorem 9.3: omega_B(psi) is a unit vector", all(is_zero_ball(sum(x * x for x in bloch(p)) - 1) for p in spinors))
check("(F) Theorem 9.3: omega_B well defined on rays (psi and c psi)",
      all(all(is_zero_ball(x - y) for x, y in zip(bloch((lam_c * p[0], lam_c * p[1])), bloch(p))) for p in spinors))
ok = True
for p in spinors[2:]:
    zeta = p[1] / p[0]
    w = bloch(p)
    n2 = abs(zeta) ** 2
    ster = [2 * zeta.real / (1 + n2), 2 * zeta.imag / (1 + n2), (1 - n2) / (1 + n2)]
    ok = ok and all(is_zero_ball(x - y) for x, y in zip(w, ster))
    ok = ok and is_zero_ball(acb(w[0], w[1]) / (1 + w[2]) - zeta)
check("(F) Theorem 9.3: omega_B(zeta) is the inverse stereographic projection, inverse (w1 + i w2)/(1 + w3)", ok)
check("(F) Theorem 9.3: zeta = infinity maps to the south pole (0, 0, -1)",
      all(is_zero_ball(x - y) for x, y in zip(bloch(spinors[1]), [arb(0), arb(0), arb(-1)])))


def push_avg(x, odd=False):
    def f(s_, analytic):
        w = (1 - s_) / (1 + s_)
        if odd:
            return w * ((x * w).exp() - (-x * w).exp()) / (1 + s_) ** 2
        return ((x * w).exp() + (-x * w).exp()) / (1 + s_) ** 2
    return acb.integral(f, acb(0), acb(1))


check("(F) Theorem 9.3: the density pi^-1 (1 + |zeta|^2)^-2 has total mass 1 (pushforward integral at x = 0)",
      is_zero_ball(push_avg(acb(0)) - 1))
ok = True
for x in [qball(Q(1)), qball(Q(-5, 2)), a]:
    ok = ok and is_zero_ball(push_avg(acb(x)) - x.sinh() / x)
check("(F) Corollary 9.4 (132): int exp(x omega_3) d mu = sinh(x)/x at x = 1, -5/2, 1/sqrt8", ok)
check("(F) Corollary 9.4 (133): int exp(-omega_3/sqrt8) d mu = r_E(z0)", is_zero_ball(push_avg(acb(-a)) - rE(z0)))
ok = True
for x in [arb(1), qball(Q(-5, 2))]:
    ok = ok and is_zero_ball(push_avg(acb(x), odd=True) / push_avg(acb(x)) - L(x))
check("(F) Corollary 9.4: the mean of omega_3 under e^{x omega_3} d mu is L(x), x = 1, -5/2", ok)
check("(F) Corollary 9.4: the average is even in x: the values at x = 1/3 and x = -1/3 agree",
      is_zero_ball(push_avg(acb(qball(Q(1, 3)))) - push_avg(acb(qball(Q(-1, 3))))))


def BJ(J, y):
    J = qball(J)
    return (2 * J + 1) / (2 * J) * coth((2 * J + 1) * y / (2 * J)) - coth(y / (2 * J)) / (2 * J)


def BJ_sum(J, y):
    J2 = int(2 * J)
    ms = [Q(k, 2) for k in range(-J2, J2 + 1, 2)]
    Jb = qball(J)
    num = sum((qball(m) / Jb) * (qball(m) * y / Jb).exp() for m in ms)
    den = sum((qball(m) * y / Jb).exp() for m in ms)
    return num / den


ys = [qball(Q(1, 3)), a, arb(2), qball(Q(-7, 5))]
check("(F) (134): B_J(y) = sum_m (m/J) e^{m y/J} / sum_m e^{m y/J}, J = 1/2, 1, 3/2, 7/2, four values of y",
      all(is_zero_ball(BJ(J, y) - BJ_sum(J, y)) for J in [Q(1, 2), Q(1), Q(3, 2), Q(7, 2)] for y in ys))
check("(F) (134): B_J(y) approaches L(y) as J grows: |B_J(1) - L(1)| decreasing in J = 1/2, 1, ..., 50",
      all(abs(BJ(Q(k, 2), arb(1)) - L(arb(1))) > abs(BJ(Q(k + 1, 2), arb(1)) - L(arb(1))) for k in range(1, 100)))
xs = [qball(Q(1, 3)), a, b, arb(2)]
check("(F) (135): (1/2) Tr exp(x sigma_3) = (e^x + e^-x)/2 = cosh x", all(is_zero_ball((x.exp() + (-x).exp()) / 2 - x.cosh()) for x in xs))
check("(F) (136): B_{1/2}(x) = tanh x", all(is_zero_ball(BJ(Q(1, 2), x) - x.tanh()) for x in xs))
check("(F) (137): B_{1/2}(x) = 2 coth 2x - coth x = 2 L(2x) - L(x)",
      all(is_zero_ball(BJ(Q(1, 2), x) - 2 * coth(2 * x) + coth(x)) and is_zero_ball(BJ(Q(1, 2), x) - 2 * L(2 * x) + L(x)) for x in xs))
check("(F) (138): sinh 2x/(2x) = (sinh x/x) cosh x",
      all(is_zero_ball((2 * x).sinh() / (2 * x) - x.sinh() / x * x.cosh()) for x in xs))
check("(F) 4 L'(2x) = L'(x) + B_{1/2}'(x), B_{1/2}' = sech^2",
      all(is_zero_ball(4 * Lp(2 * x) - Lp(x) - 1 / x.cosh() ** 2) for x in xs))
check("(F) the mean moment of a dipole of moment 2 is d/dx log(sinh 2x/2x) = 2 L(2x) (difference quotient form)",
      all(is_zero_ball(2 * (2 * x).cosh() / (2 * x).sinh() - 1 / x - 2 * L(2 * x)) for x in xs))
# spectral forms of cosh x and tanh x with rigorous tails
ok = True
for x in [a, arb(1)]:
    Pc = arb(1)
    Ssum = arb(0)
    s_inv = arb(0)
    NC = 3000
    for n in range(1, NC + 1):
        nu2 = qball(Q((2 * n - 1) ** 2, 4))
        Pc *= 1 + x * x / (pi ** 2 * nu2)
        Ssum += 1 / (pi ** 2 * nu2 + x * x)
        s_inv += 1 / nu2
    tail_inv = (pi ** 2 / 2 - s_inv) / pi ** 2
    ok = ok and in_bracket(x.cosh(), Pc, Pc * (x * x * tail_inv).exp())
    lo_t = 2 * x * (Ssum + tail_inv - x * x * 1 / (3 * pi ** 4 * qball(Q(2 * NC - 1, 2)) ** 3))
    hi_t = 2 * x * (Ssum + tail_inv)
    ok = ok and in_bracket(x.tanh(), lo_t, hi_t)
check("(F) (135)-(136): cosh x = det(I + x^2/A_DN) and tanh x = 2x Tr((A_DN + x^2)^-1) "
      "with rigorous tails, x = 1/sqrt8, 1", ok)
ok = True
for x in xs:
    Ex, Emx = x.exp(), (-x).exp()
    for p in spinors:
        lhs = Theta((Ex * p[0], Emx * p[1]))
        tp = Theta(p)
        rhs = (Emx * tp[0], Ex * tp[1])
        ok = ok and all(is_zero_ball(u - v) for u, v in zip(lhs, rhs))
check("(F) Proposition 9.5 (i): Theta exp(x sigma_3) = exp(-x sigma_3) Theta for real x", ok)
# Proposition 9.7
check("(F) Proposition 9.7: S fixes i: -1/i = i, and S(S tau) = tau",
      is_zero_ball(S(I) - I) and all(is_zero_ball(S(S(t)) - t) for t in samples))
check("(F) Proposition 9.7: delta has no fixed point on C^x and delta^2 = id",
      all(not (-t - t).contains(0) and is_zero_ball(-(-t) - t) for t in samples))
Z0 = Q(376730313412, 10 ** 9)
svals = [Q(1, 3), Q(1), Q(5, 2), Q(7, 11)]
check("(F) Proposition 9.7 (iv): -1/(-s) = 1/s, Z0^2/(4 (Z0 s/2)) = Z0/(2s), fixed points H = -1, s = 1, Z = Z0/2",
      all(-1 / (-s_) == 1 / s_ and Z0 ** 2 / (4 * (Z0 * s_ / 2)) == Z0 / (2 * s_) for s_ in svals)
      and 1 / Q(-1) == Q(-1) and 1 / Q(1) == Q(1) and Z0 ** 2 / (4 * (Z0 / 2)) == Z0 / 2)
check("(F) Remark 9.6: Z0/2 = 188.365... Ohm is within 0.3 Ohm of 60 pi",
      abs(qball(Z0 / 2) - 60 * pi) < qball(Q(3, 10)))
check("(F) Remark 9.6: tanh 2K_sd = |z0| attaches the point to the Ising involution, sinh 2K_sd is its fixed point 1",
      is_zero_ball((2 * K).tanh() - abs(z0)) and is_zero_ball((2 * K).sinh() - 1))

print("C0             =", C0.str(60, radius=False))
print("companion      =", comp.str(60, radius=False))
print("K_sd           =", K.str(60, radius=False))
print("R_00(1/8)      =", Rs.str(60, radius=False))
if failures:
    print(f"FAILED {len(failures)} of {count} checks")
    for f_ in failures:
        print("  FAIL:", f_)
    sys.exit(1)
print(f"ALL {count} SECTION 8/9 CHECKS PASSED (precision {ctx.prec} bits)")
