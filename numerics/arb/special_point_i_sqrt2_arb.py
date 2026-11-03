#!/usr/bin/env python3
"""Draft 0.10r5 numerical certificates (exact rationals and Arb real balls).

These checks certify scalar enclosures, not the analytic/operator identities.
"""
from fractions import Fraction
from math import factorial
import sys
import flint
from flint import arb, acb, ctx

ctx.prec = 256
failures = []

def check(desc, condition):
    state = bool(condition)
    print(f"{'PASS' if state else 'FAIL'}: {desc}")
    if not state:
        failures.append(desc)

def qball(q):
    q = Fraction(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

def bound(name, x, lo, hi):
    check(name, x > qball(Fraction(lo)) and x < qball(Fraction(hi)))
    print(f"    Arb enclosure: {x.str(50)}")

print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

def denominator(n):
    return 8**n * factorial(2*n + 1)

check("denominator first five integers",
      [denominator(n) for n in range(5)] ==
      [1, 48, 7680, 2580480, 1486356480])
check("integer recurrence n=0,...,39 (Lean proof is universal)",
      all(denominator(n+1) == 8*(2*n+2)*(2*n+3)*denominator(n) for n in range(40)))

N = 11
S = sum((Fraction(1, denominator(n)) for n in range(N+1)), Fraction(0))
b_next = Fraction(1, denominator(N+1))
q_tail = Fraction(1, 8*(2*N+4)*(2*N+5))
upper = S + b_next / (1-q_tail)
check("rational remainder: 0 < q_tail < 1", 0 < q_tail < 1)
check("rational remainder interval nonempty", S < upper)

a = arb(8).rsqrt()
r = a.sinh() / a
check("Arb: rational series enclosure strictly contains sinh(a)/a",
      qball(S) < r < qball(upper))
bound("Eulerian scalar r_E(i/sqrt(2))", r,
      "1.020963929865019510478664635180420",
      "1.020963929865019510478664635180422")

mean = a.coth() - 1/a
variance = 1/(a*a) - 1/(a.sinh()*a.sinh())
trace = mean/(2*a)
bound("Langevin mean at 1/sqrt(8)", mean,
      "0.116880584703933019708531813861790",
      "0.116880584703933019708531813861793")
bound("orientation variance at 1/sqrt(8)", variance,
      "0.325162496653669143961633763850837",
      "0.325162496653669143961633763850840")
bound("Dirichlet resolvent trace scalar", trace,
      "0.165294108066399398665502780884923",
      "0.165294108066399398665502780884927")

hs_squared = (2*trace - variance)/(4*a*a)
bound("Dirichlet squared Hilbert-Schmidt norm", hs_squared,
      "0.010851438958259306738743595838020",
      "0.010851438958259306738743595838023")

# Draft 0.10r5: prove each 50-significant-digit printed decimal is correctly rounded.
# Comparisons are certified ball inequalities against exact rational half-ULP bounds.
def rounded_50(name, x, printed):
    digits = len(printed.replace(".", "").lstrip("0"))
    check(name + ": exactly 50 significant digits", digits == 50)
    center = Fraction(printed)
    n_decimal_places = len(printed.partition(".")[2])
    half_ulp = Fraction(1, 2 * 10**n_decimal_places)
    lo = center - half_ulp
    hi = center + half_ulp
    check(name + ": correct rounding to 50 significant digits",
          x > qball(lo) and x < qball(hi))

rounded_50("Draft 0.10r5 Eq. (8) rE", r,
           "1.0209639298650195104786646351804211019462043266699")
rounded_50("Draft 0.10r5 Eq. (44) Langevin", mean,
           "0.11688058470393301970853181386179164401493872379933")
rounded_50("Draft 0.10r5 Eq. (45) variance", variance,
           "0.32516249665366914396163376385083845935142050373689")
rounded_50("Draft 0.10r5 resolvent trace", trace,
           "0.16529410806639939866550278088492457407260894951106")
rounded_50("Draft 0.10r5 HS norm squared", hs_squared,
           "0.010851438958259306738743595838021377587594790570479")

tau = acb(0, 2*a)
cm_j = tau.modular_j()
check("Klein modular j at i/sqrt(2) overlaps 8000", cm_j.overlaps(acb(8000)))
check("Klein modular j within 1e-40 of 8000", abs(cm_j - 8000) < qball("1e-40"))
print(f"    CM modular j enclosure: {cm_j}")

kappa = arb.pi()*a
bound("arithmetic scalar pi/sqrt(8)", kappa,
      "1.110720734539591561753970247",
      "1.110720734539591561753970249")

print("Not proved here: class-number formula, exact modular equality j(z0)=8000, operator-domain theorems.")
print("ALL NUMERICAL CHECKS PASSED" if not failures else f"FAILED CHECKS: {failures}")
sys.exit(0 if not failures else 1)
