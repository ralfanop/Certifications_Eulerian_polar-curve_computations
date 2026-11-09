#!/usr/bin/env python3
"""Manuscript 14, version 14.119 (9 November 2026): Proposition 10.2, the Parry index of the Eulerian
values sinh(x)/x, displays (176)-(177).

Exact rational arithmetic and Arb balls at 2000 bits (python-flint 0.9.0). For x > 0 put
beta = sinh(x)/x, eps = beta - 1 = (sinh x - x)/x and rho(x) = log(1/eps)/log(beta), the quotient of
(176); F_m(t) = t^(m-1)(t-1) - 1 and beta_m is its zero in (1, 2), so that beta < beta_m exactly when
beta^(m-1)(beta-1) < 1 (the general equivalence and the greedy word are the Lean module
V14119ParryIndexCertificate).

  (A) The two values of the statement: rho(1/sqrt2) in (30, 31), hence n(1/sqrt2) = 31, with
      beta_E^30 (beta_E - 1) < 1 < beta_E^31 (beta_E - 1) and the defect 1 - beta_E^30 (beta_E - 1)
      inside the bounds (168) of Theorem 10.1; rho(1/sqrt8) in (186, 187), hence n(1/sqrt8) = 187.
  (B) The rational certificate of the proof at x = 1/sqrt8: the first five terms of
      r_E(z_0) = sum_k 1/[8^k (2k+1)!] and the tail bound t_5 * 1248/1247 < 1e-12 (ratio at most 1/1248
      for k >= 5) give 1020963929/10^9 < r_E(z_0) < 1020963930/10^9; exactly, F_187 < -1/200 at the
      right endpoint and F_188 > 1/100 at the left one; the Arb value of sinh(a)/a, a = 1/sqrt8, lies
      in that interval; the bracket 10854/10^4 < beta_E < 1085445/10^6 of the proof of Theorem 10.1.
  (C) (176) and the greedy word against the definition: for x = k/100, k = 1, ..., 175 (all with
      sinh(x)/x < beta_2 = (1 + sqrt5)/2), the ball of rho(x) contains no integer, n = ceil(rho) satisfies
      beta^(n-1)(beta-1) < 1 < beta^n (beta-1), and the first n + 1 greedy digits of 1 in base beta,
      every floor decided by the ball, are 1 0^(n-1) 1.
  (D) (177): with t = x^2, eps = (t/6) E(t), E(t) = 1 + t/20 + t^2/840 + ..., and
      eps/log(1 + eps) = 1 + eps/2 - eps^2/12 + ..., exact series arithmetic in Q gives
      rho = (6/t)[log(6/t) - log E(t)] mu(t) with mu(t) = 1 + t/30 + ..., -log E(t) = -t/20 + ...,
      hence the coefficients 6, 1/5 and -3/10 of (177); the next-order term t (c_1 log(6/t) + c_0) is
      computed exactly, and at x = 10^-1, ..., 10^-6 the Arb remainder of (177) is below
      x^2 log(6/x^2)/100 and agrees with that next-order term to within x^4 log(6/x^2)^2.
"""
from fractions import Fraction as Q
from math import factorial
import sys
import flint
from flint import arb, fmpz, ctx

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
    return arb(fmpz(q.numerator)) / arb(fmpz(q.denominator))


def beta_of(x):
    return x.sinh() / x


def rho(x):
    """The quotient log(1/(beta - 1))/log(beta) of (176), with beta - 1 = (sinh x - x)/x."""
    eps = (x.sinh() - x) / x
    return -eps.log() / (1 + eps).log()


def ceil_ball(r):
    """The integer n with n - 1 < r < n, if the ball r decides it, else None."""
    n = int(float(r.mid())) + 1
    if r > n - 1 and r < n:
        return n
    return None


def greedy_digits(beta, count_):
    """The first count_ greedy digits of 1 in base beta (1 < beta < 2); None if a floor is undecided."""
    y, out = arb(1), []
    for _ in range(count_):
        z = beta * y
        if z < 1:
            out.append(0)
            y = z
        elif z > 1 and z < 2:
            out.append(1)
            y = z - 1
        else:
            return None
    return out


print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")
SQRT2 = arb(2).sqrt()
a = 1 / arb(8).sqrt()
b = 1 / SQRT2
F = lambda m, t: t ** (m - 1) * (t - 1) - 1

# ---------------------------------------------------------------------------------------------------
print("(A) the two values of Proposition 10.2")
rb, ra = rho(b), rho(a)
print(f"    rho(1/sqrt2) = {rb.str(20, radius=False)},  rho(1/sqrt8) = {ra.str(20, radius=False)}")
check("(A) 30 < rho(1/sqrt2) < 31, so n(1/sqrt2) = ceil(rho) = 31", ceil_ball(rb) == 31)
check("(A) 186 < rho(1/sqrt8) < 187, so n(1/sqrt8) = ceil(rho) = 187", ceil_ball(ra) == 187)
bE = beta_of(b)
check("(A) beta_E^30 (beta_E - 1) < 1 < beta_E^31 (beta_E - 1), i.e. beta_32 < beta_E < beta_31",
      bE ** 30 * (bE - 1) < 1 and bE ** 31 * (bE - 1) > 1)
dE = 1 - bE ** 30 * (bE - 1)
check("(A) the defect 1 - beta_E^30 (beta_E - 1) lies in the bounds (168) of Theorem 10.1",
      dE > qball(Q(313240, 10 ** 9)) and dE < qball(Q(313241, 10 ** 9)))
bZ = beta_of(a)
check("(A) r_E(z_0)^186 (r_E(z_0) - 1) < 1 < r_E(z_0)^187 (r_E(z_0) - 1), i.e. beta_188 < r_E(z_0) < beta_187",
      bZ ** 186 * (bZ - 1) < 1 and bZ ** 187 * (bZ - 1) > 1)

# ---------------------------------------------------------------------------------------------------
print("(B) the rational certificates of the proof")
t = [Q(1, 8 ** k * factorial(2 * k + 1)) for k in range(12)]
check("(B) ratio t_(k+1)/t_k = 1/[8(2k+2)(2k+3)] at most 1/1248 for k >= 5",
      all(t[k + 1] / t[k] == Q(1, 8 * (2 * k + 2) * (2 * k + 3)) and t[k + 1] / t[k] <= Q(1, 1248)
          for k in range(5, 11)))
s4 = sum(t[:5])
tail = t[5] * Q(1248, 1247)
check("(B) the tail after the first five terms is below t_5 * 1248/1247 < 1e-12", tail < Q(1, 10 ** 12))
lo, hi = Q(1020963929, 10 ** 9), Q(1020963930, 10 ** 9)
check("(B) 1020963929/10^9 < s_4 and s_4 + tail < 1020963930/10^9", lo < s4 and s4 + tail < hi)
check("(B) the Arb value of sinh(a)/a, a = 1/sqrt8, lies in (1020963929/10^9, 1020963930/10^9)",
      bZ > qball(lo) and bZ < qball(hi))
check("(B) exactly, F_187(1020963930/10^9) < -1/200", F(187, hi) < Q(-1, 200))
check("(B) exactly, F_188(1020963929/10^9) > 1/100", F(188, lo) > Q(1, 100))
check("(B) the bracket 10854/10^4 < beta_E < 1085445/10^6 of the proof of Theorem 10.1",
      bE > qball(Q(10854, 10 ** 4)) and bE < qball(Q(1085445, 10 ** 6)))

# ---------------------------------------------------------------------------------------------------
print("(C) (176) and the greedy word for x = k/100, k = 1, ..., 175")
phi = (1 + arb(5).sqrt()) / 2
ok_dom = ok_ceil = ok_def = ok_word = True
largest = 0
for k in range(1, 176):
    x = arb(k) / 100
    beta = beta_of(x)
    if not (beta > 1 and beta < phi):
        ok_dom = False
        print(f"    k = {k}: sinh(x)/x not in (1, beta_2)")
        continue
    n = ceil_ball(rho(x))
    if n is None:
        ok_ceil = False
        print(f"    k = {k}: the ball of rho contains an integer")
        continue
    largest = max(largest, n)
    if not (beta ** (n - 1) * (beta - 1) < 1 and beta ** n * (beta - 1) > 1):
        ok_def = False
        print(f"    k = {k}: n = {n} fails beta_(n+1) < beta < beta_n")
    d = greedy_digits(beta, n + 1)
    if d is None or d != [1] + [0] * (n - 1) + [1]:
        ok_word = False
        print(f"    k = {k}: greedy word differs from 1 0^(n-1) 1")
check("(C) every sinh(k/100)/(k/100) lies in (1, beta_2)", ok_dom)
check("(C) no ball of rho(k/100) contains an integer, so n = ceil(rho) is decided", ok_ceil)
check("(C) n = ceil(rho) satisfies beta^(n-1)(beta-1) < 1 < beta^n (beta-1), the definition of n(x)", ok_def)
check(f"(C) the first n + 1 greedy digits are 1 0^(n-1) 1, every floor decided (largest n = {largest})",
      ok_word)

# ---------------------------------------------------------------------------------------------------
print("(D) the asymptotics (177)")
N = 5                                       # series truncated after t^(N-1)


def mul(p, q):
    r = [Q(0)] * N
    for i in range(N):
        for j in range(N - i):
            r[i + j] += p[i] * q[j]
    return r


def inv(p):
    r = [Q(0)] * N
    r[0] = 1 / p[0]
    for n_ in range(1, N):
        r[n_] = -sum(p[j] * r[n_ - j] for j in range(1, n_ + 1)) / p[0]
    return r


def compose(f, g):
    """f(g(t)) for a series f in one variable and g with g(0) = 0."""
    r, gp = [Q(0)] * N, [Q(1)] + [Q(0)] * (N - 1)
    for i in range(N):
        r = [r[j] + f[i] * gp[j] for j in range(N)]
        gp = mul(gp, g)
    return r


E = [6 * Q(1, factorial(2 * k + 3)) for k in range(N)]                 # E(t) = 6 eps/t
check("(D) E(t) = 1 + t/20 + t^2/840 + ...", E[0] == 1 and E[1] == Q(1, 20) and E[2] == Q(1, 840))
log1p = [Q(0)] + [Q((-1) ** (k + 1), k) for k in range(1, N)]
lam = [-c for c in compose(log1p, [Q(0)] + E[1:])]                   # -log E(t)
eps = [Q(0)] + [E[k] / 6 for k in range(N - 1)]                       # eps(t) = (t/6) E(t)
G = inv([Q((-1) ** k, k + 1) for k in range(N)])                      # eps/log(1 + eps) as a series in eps
check("(D) eps/log(1 + eps) = 1 + eps/2 - eps^2/12 + ...", G[0] == 1 and G[1] == Q(1, 2) and G[2] == Q(-1, 12))
mu = mul(compose(G, eps), inv(E))                                     # mu(t) = G(eps(t))/E(t)
check("(D) -log E(t) = -t/20 + ...", lam[0] == 0 and lam[1] == Q(-1, 20))
check("(D) mu(t) = 1 + t/30 + ...", mu[0] == 1 and mu[1] == Q(1, 30))
check("(D) the coefficients of (177): 6 mu_1 = 1/5 and 6 lambda_1 = -3/10", 6 * mu[1] == Q(1, 5) and
      6 * lam[1] == Q(-3, 10))
c1 = 6 * mu[2]                                                        # next order: t (c1 log(6/t) + c0)
c0 = 6 * (lam[2] + lam[1] * mu[1])
print(f"    next-order term of (177): x^2 [({c1}) log(6/x^2) + ({c0})]")
good_o = good_n = True
for j in range(1, 7):
    x = arb(10) ** (-j)
    Lx = (6 / x ** 2).log()
    rem = rho(x) - (6 / x ** 2 * Lx + Lx / 5 - qball(Q(3, 10)))
    if not abs(rem) < x ** 2 * Lx / 100:
        good_o = False
    if not abs(rem - x ** 2 * (qball(c1) * Lx + qball(c0))) < x ** 4 * Lx ** 2:
        good_n = False
    print(f"    x = 1e-{j}: remainder of (177) = {rem.str(8, radius=False)},  x^2 log(6/x^2) = "
          f"{(x ** 2 * Lx).str(8, radius=False)}")
check("(D) at x = 10^-1, ..., 10^-6 the remainder of (177) is below x^2 log(6/x^2)/100", good_o)
check("(D) and it agrees with the exact next-order term to within x^4 log(6/x^2)^2", good_n)

print(f"python-flint {flint.__version__}, precision {PREC} bits, {count} checks")
if failures:
    print(f"FAILED: {len(failures)} check(s)")
    for f_ in failures:
        print("   ", f_)
    sys.exit(1)
print("ALL VERSION-14.119 PROPOSITION 10.2 CHECKS PASSED AT 2000 BITS")
