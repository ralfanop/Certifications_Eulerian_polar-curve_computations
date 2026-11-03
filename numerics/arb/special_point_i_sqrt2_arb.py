#!/usr/bin/env python3
"""Draft 0.10r1 numerical certificates (exact rationals and Arb real balls).

These checks certify scalar enclosures, not the analytic/operator identities.
"""
from fractions import Fraction
from math import factorial
import sys
import flint
from flint import arb, ctx

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

kappa = arb.pi()*a
bound("arithmetic scalar pi/sqrt(8)", kappa,
      "1.110720734539591561753970247",
      "1.110720734539591561753970249")

print("Not proved here: class-number formula, j(z0)=8000, operator-domain theorems.")
print("ALL NUMERICAL CHECKS PASSED" if not failures else f"FAILED CHECKS: {failures}")
sys.exit(0 if not failures else 1)
