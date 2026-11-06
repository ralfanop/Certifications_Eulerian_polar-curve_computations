#!/usr/bin/env python3
"""Manuscript 14, Proposition 6.5 (A convergent even-zeta expansion), displays (77)-(78).

Certificates, at 2000 bits of Arb working precision and in exact rational arithmetic, for

    log r_E(z_0) = sum_{m>=1} (-1)^{m+1} zeta(2m) / [m (8 pi^2)^m]          (77, zeta form)
                 = sum_{m>=1} B_{2m} / [2^{m+1} m (2m)!]                    (77, Bernoulli form)
                 = 1/48 - 1/11520 + 1/1451520 - 1/154828800 + 1/15328051200
                   - 691/1004293914624000 + 1/133905855283200
                   - 3617/43706871164436480000 + ...                        (78)

with r_E(z_0) = sinh(a)/a, a = 1/sqrt(8).  The checks are:
  (A) exact rationals: the Bernoulli numbers B_2..B_16, the eight displayed terms of (78),
      and the coefficients c_m of zeta(2m) = c_m pi^{2m} for m = 1..8 (Euler's formula);
  (B) zeta(2m) as a Dirichlet series: the Arb value of zeta(2m) lies between the exact
      rational partial sum sum_{n<=K} n^{-2m} plus the integral tail bounds
      (K+1)^{1-2m}/(2m-1) and K^{1-2m}/(2m-1), m = 1..8, K = 2000;
  (C) termwise agreement of the zeta form and the Bernoulli form in Arb, m = 1..40;
  (D) the sum: log(sinh(a)/a) in Arb lies inside the exact rational partial sum of the
      Bernoulli form with an exact rational tail majorant (N = 60 terms), and between
      the partial sum of the eight displayed terms and that sum plus the ninth term
      (alternating series with decreasing terms);
  (E) the value of log r_E(z_0) to 590 digits, with correct rounding proved by the ball.
Every Arb quantity is a ball (midpoint + rigorous radius); comparisons between balls and
exact rationals are certified ball inequalities.  Requires python-flint 0.9.0.
"""
from fractions import Fraction as Q
from decimal import Decimal
from math import factorial
import sys
import flint
from flint import arb, ctx

PREC = 2000
ctx.prec = PREC
sys.set_int_max_str_digits(0)   # the exact Dirichlet partial sums have numerators beyond 4300 digits
failures = []

def check(desc, cond):
    ok = bool(cond)
    print(f"{'PASS' if ok else 'FAIL'}: {desc}")
    if not ok:
        failures.append(desc)

def qball(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)      # exact integers, then one rounded division

print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

# ---------------------------------------------------------------- exact Bernoulli numbers
def bernoulli_list(n):
    """B_0..B_n by the Akiyama-Tanigawa algorithm (B_1 = +1/2 convention; even indices unaffected)."""
    A = [Q(0)]*(n+1); B = []
    for m in range(n+1):
        A[m] = Q(1, m+1)
        for j in range(m, 0, -1):
            A[j-1] = j*(A[j-1]-A[j])
        B.append(A[0])
    return B

NMAX = 130
B = bernoulli_list(NMAX)

def term_bernoulli(m):          # B_{2m} / [2^{m+1} m (2m)!]
    return B[2*m] / (2**(m+1) * m * factorial(2*m))

def zeta_coefficient(m):        # c_m with zeta(2m) = c_m pi^{2m}  (Euler)
    return (-1)**(m+1) * B[2*m] * 2**(2*m) / (2*factorial(2*m))

# (A) exact rationals stated in the manuscript
stated_B = {2: Q(1, 6), 4: Q(-1, 30), 6: Q(1, 42), 8: Q(-1, 30), 10: Q(5, 66),
            12: Q(-691, 2730), 14: Q(7, 6), 16: Q(-3617, 510)}
for k, v in stated_B.items():
    check(f"B_{k} = {v} (exact)", B[k] == v)

stated_terms = [Q(1, 48), Q(-1, 11520), Q(1, 1451520), Q(-1, 154828800), Q(1, 15328051200),
                Q(-691, 1004293914624000), Q(1, 133905855283200), Q(-3617, 43706871164436480000)]
for m, t in enumerate(stated_terms, start=1):
    check(f"(78) term m={m}: B_{2*m}/[2^{m+1} m (2m)!] = {t} (exact)", term_bernoulli(m) == t)

stated_zeta = {1: Q(1, 6), 2: Q(1, 90), 3: Q(1, 945), 4: Q(1, 9450), 5: Q(1, 93555),
               6: Q(691, 638512875), 7: Q(2, 18243225), 8: Q(3617, 325641566250)}
for m, c in stated_zeta.items():
    check(f"Euler: zeta({2*m}) = {c} * pi^{2*m} (exact coefficient from B_{2*m})", zeta_coefficient(m) == c)

# the three added terms as -zeta(12)/[6(8 pi^2)^6], zeta(14)/[7(8 pi^2)^7], -zeta(16)/[8(8 pi^2)^8]
for m in (6, 7, 8):
    check(f"term m={m} equals (-1)^(m+1) c_m / (m 8^m) exactly (powers of pi cancel)",
          (-1)**(m+1) * zeta_coefficient(m) / (m * 8**m) == stated_terms[m-1])

# ---------------------------------------------------------------- (B) zeta(2m) as a Dirichlet series
K = 2000
pi = arb.pi()
for m in range(1, 9):
    s = 2*m
    partial = sum((Q(1, n**s) for n in range(1, K+1)), Q(0))
    lo = partial + Q(1, (K+1)**(s-1) * (s-1))      # integral bounds for the tail sum_{n>K} n^{-s}
    hi = partial + Q(1, K**(s-1) * (s-1))
    z = arb(s).zeta()
    check(f"zeta({s}) (Arb) inside the exact Dirichlet-series enclosure with K={K} terms",
          qball(lo) < z and z < qball(hi))
    check(f"zeta({s}) (Arb) overlaps the closed form c_m pi^{s}", z.overlaps(qball(zeta_coefficient(m)) * pi**s))

# ---------------------------------------------------------------- (C) zeta form vs Bernoulli form, termwise
eight_pi2 = 8*pi*pi
for m in range(1, 41):
    zeta_term = (-1)**(m+1) * arb(2*m).zeta() / (m * eight_pi2**m)
    check(f"m={m}: (-1)^(m+1) zeta(2m)/[m (8 pi^2)^m] overlaps B_(2m)/[2^(m+1) m (2m)!]",
          zeta_term.overlaps(qball(term_bernoulli(m))))

# ---------------------------------------------------------------- (D) the sum
a = arb(8).rsqrt()                          # a = 1/sqrt(8)
rE = a.sinh() / a                           # r_E(z_0) = sinh(a)/a
logrE = rE.log()
check("r_E(z_0) = sinh(a)/a > 1", rE > arb(1))

# exact rational partial sum of the Bernoulli form with N terms and an exact tail majorant:
# |t_m| = zeta(2m)/[m (8 pi^2)^m] <= 2/[(N+1) 78^m] for m > N (zeta(2m) <= zeta(2) < 2, 8 pi^2 > 78)
N = 60
S_N = sum((term_bernoulli(m) for m in range(1, N+1)), Q(0))
r = Q(1, 78)
tail = Q(2, N+1) * r**(N+1) / (1 - r)
check("8 pi^2 > 78 (Arb)", eight_pi2 > arb(78))
check("zeta(2) < 2 (Arb)", arb(2).zeta() < arb(2))
check(f"log r_E(z_0) inside the exact rational enclosure S_{N} -/+ tail of the Bernoulli series",
      qball(S_N - tail) < logrE and logrE < qball(S_N + tail))
print(f"    tail majorant after {N} terms: {float(tail):.3e}")

# the eight displayed terms: alternating series with decreasing moduli
S_8 = sum(stated_terms, Q(0))
t_9 = term_bernoulli(9)
check("ninth term positive and smaller in modulus than the eighth",
      t_9 > 0 and t_9 < -stated_terms[7])
check("moduli of the terms decrease for m = 1..60 (exact rationals)",
      all(abs(term_bernoulli(m+1)) < abs(term_bernoulli(m)) for m in range(1, N)))
check("S_8 < log r_E(z_0) < S_8 + t_9  (remainder of the eight displayed terms)",
      qball(S_8) < logrE and logrE < qball(S_8 + t_9))
print(f"    S_8 = {S_8}")
print(f"    t_9 = {t_9}")

# ---------------------------------------------------------------- (E) decimal value of log r_E(z_0)
def radius_bits(x):
    rr = x.rad()
    return float(arb(rr).log()/arb(2).log()) if rr > 0 else float('-inf')
print(f"    log r_E(z_0) = {logrE.str(60)}  (radius 2^{radius_bits(logrE):.1f})")
check("log r_E(z_0): enclosure radius below 2^-1980", logrE.rad() < arb(2)**(-1980))
# 590 significant digits: the half-ULP 5e-592 exceeds the ball radius (about 2^-1997 = 6e-602),
# so the rounding is certified; 600 digits would be within the radius.
s590 = logrE.str(590, radius=False)
d590 = Decimal(s590); center = Q(d590); half = Q(1, 2*10**(-d590.as_tuple().exponent))
check("590-digit value of log r_E(z_0) correctly rounded (certified half-ULP comparison)",
      logrE > qball(center-half) and logrE < qball(center+half))
print(f"    log r_E(z_0) to 590 digits: {s590}")
print(f"    r_E(z_0) to 60 digits: {rE.str(60, radius=False)}")

print(f"python-flint {flint.__version__}, precision {ctx.prec} bits")
if failures:
    print(f"FAILED: {len(failures)} check(s)"); sys.exit(1)
print("ALL PROPOSITION 6.5 ZETA/BERNOULLI CHECKS PASSED AT 2000 BITS")
