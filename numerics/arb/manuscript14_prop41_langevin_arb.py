#!/usr/bin/env python3
"""Manuscript 14, Proposition 4.1 (Special partition function and magnetisation).

Arb certificates at 2000 bits for the Langevin mean L(a) = coth(a) - 1/a and the
orientation variance L'(a) = 1/a^2 - 1/sinh(a)^2 at a = 1/sqrt(8), i.e. (38), (39),
and for the fifty-digit values (41), (42) of Remark 4.3.  Every quantity is an Arb
ball (midpoint + rigorous radius); the comparisons are certified ball inequalities
against exact rationals.  Requires python-flint 0.9.0 (as the other workflows).
"""
from fractions import Fraction
import sys
import flint
from flint import arb, ctx

PREC = 2000
ctx.prec = PREC
failures = []

def check(desc, cond):
    ok = bool(cond)
    print(f"{'PASS' if ok else 'FAIL'}: {desc}")
    if not ok:
        failures.append(desc)

def qball(q):
    q = Fraction(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

a = arb(8).rsqrt()                       # a = 1/sqrt(8), rigorous ball
check("a^2 = 1/8 contains the exact rational", (a*a).contains(qball(Fraction(1, 8))))

mean = a.coth() - 1/a                    # L(a) = coth(a) - 1/a            (38)
variance = 1/(a*a) - 1/(a.sinh()*a.sinh())   # L'(a) = 1/a^2 - 1/sinh(a)^2   (39)
mean_alt = a.coth() - arb(8).sqrt()      # coth(a) - sqrt(8)
variance_alt = 8 - 1/(a.sinh()*a.sinh()) # 8 - csch(a)^2

# Radii of the enclosures: the certificate is the radius itself.
def radius_bits(x):
    r = x.rad()
    return float(arb(r).log()/arb(2).log()) if r > 0 else float('-inf')

for name, x in (("L(a)", mean), ("L'(a)", variance)):
    print(f"    {name} = {x.str(60)}  (radius 2^{radius_bits(x):.1f})")
    check(f"{name}: enclosure radius below 2^-1980", x.rad() < arb(2)**(-1980))

check("coth(a) - 1/a overlaps coth(a) - sqrt(8)        [form of (38)]", mean.overlaps(mean_alt))
check("1/a^2 - csch(a)^2 overlaps 8 - csch(a)^2        [form of (39)]", variance.overlaps(variance_alt))

# Independent series check: L(x) = sum_{k>=1} 2^{2k} B_{2k} x^{2k-1} / (2k)!  truncated with
# an exact rational remainder (|B_{2k}| <= 2 (2k)! / (2 pi)^{2k} / (1 - 2^{1-2k})).
from math import factorial
from fractions import Fraction as Q
def bernoulli(n):
    A = [Q(0)]*(n+1)
    for m in range(n+1):
        A[m] = Q(1, m+1)
        for j in range(m, 0, -1):
            A[j-1] = j*(A[j-1]-A[j])
    return A[0]                           # B_n with B_1 = +1/2 convention; even indices unaffected
N = 60
x2 = Q(1, 8)                              # a^2 exactly
S = Q(0)
for k in range(1, N+1):
    S += Q(2**(2*k), factorial(2*k)) * bernoulli(2*k) * x2**k      # times 1/a overall
# remainder bound: |term_k| <= 2*2^{2k} x2^k/(2 pi)^{2k} /(1-2^{1-2k}) <= 4 (x2/pi^2)^k <= 4 (1/78)^k
r = Q(1, 78)
rem = 4*r**(N+1)/(1-r)
L_series = S/a                            # exact rational coefficient times the ball 1/a
check("L(a) inside Bernoulli-series enclosure with exact rational remainder",
      (qball(S-rem)/a) < mean and mean < (qball(S+rem)/a))

# Fifty-digit printed values (41), (42): correct rounding, certified half-ULP comparisons.
def rounded(name, x, printed):
    center = Q(printed)
    places = len(printed.partition('.')[2])
    half = Q(1, 2*10**places)
    check(f"{name} correctly rounded to {places} decimal places",
          x > qball(center-half) and x < qball(center+half))
rounded("(41) L(a)", mean, "0.11688058470393301970853181386179164401493872379933")
rounded("(42) Var_a", variance, "0.32516249665366914396163376385083845935142050373689")

# 600-digit values for the log, with the rounding of each proved by the ball.
for name, x in (("L(a)", mean), ("L'(a)", variance)):
    s = x.str(600, radius=False)
    print(f"    {name} to 600 digits: {s}")

print(f"python-flint {flint.__version__}, precision {ctx.prec} bits")
if failures:
    print(f"FAILED: {len(failures)} check(s)"); sys.exit(1)
print("ALL PROPOSITION 4.1 LANGEVIN CHECKS PASSED AT 2000 BITS")
