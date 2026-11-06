#!/usr/bin/env python3
"""Sonine §4: exact Bessel coefficient map and compact-disk tail bounds.

The script proves the asserted rational inequalities by exact Fraction
arithmetic for finite test radii; at the designated sample points Arb
supplies rigorous ball enclosures for sin(R)/R and sinh(R)/R.

Analytic convergence for all complex radii and arbitrary even-entire
coefficients requires Lean lemmas and is not claimed from finite tests.
"""
from fractions import Fraction as Q
from math import factorial
from flint import arb, ctx
import flint

ctx.prec = 2000
passed = 0

def check(label, ok):
    global passed
    if not bool(ok):
        raise AssertionError("FAIL " + label)
    passed += 1
    print(f"PASS {passed:02d}: {label}")

def qball(q):
    q=Q(q)
    return arb(str(q.numerator))/arb(str(q.denominator))

def moment(n):
    return Q(4**n * factorial(n)**2, factorial(2*n+1))

def cyl_i(n):
    return Q(1,4**n*factorial(n)**2)

def sph_i(n):
    return Q(1,factorial(2*n+1))

check("exact modified and ordinary Bessel maps through n=180",
      all(moment(n)*cyl_i(n) == sph_i(n) and
          moment(n)*((-1)**n*cyl_i(n))==(-1)**n*sph_i(n)
          for n in range(181)))

radii=(1,2,4,8)
cutoffs=(12,16,24,30)
check("positive geometric spherical tail bounds on 16 disks",
      all(Q(R**(2*N+2),factorial(2*N+3)) > 0 and
          Q(R*R,(2*N+4)*(2*N+5)) < 1
          for R in radii for N in cutoffs))

check("positive geometric cylindrical I0 tail bounds on 16 disks",
      all(Q(R**(2*N+2),4**(N+1)*factorial(N+1)**2) > 0 and
          Q(R*R,4*(N+2)**2) < 1
          for R in radii for N in cutoffs))

for R in radii:
    value_i=arb(R).sinh()/arb(R)
    value_j=arb(R).sin()/arb(R)
    for N in cutoffs:
        term=lambda n: Q(R**(2*n),factorial(2*n+1))
        S=sum((term(n) for n in range(N+1)),Q(0))
        q=Q(R*R,(2*N+4)*(2*N+5))
        upper=S+term(N+1)/(1-q)
        check(f"strict 2000-bit modified spherical enclosure R={R}, N={N}",
              qball(S) < value_i < qball(upper))
        alt=sum(((-1)**n*term(n) for n in range(N+1)),Q(0))
        low,high=(alt-term(N+1),alt) if N%2==0 else (alt,alt+term(N+1))
        check(f"strict 2000-bit ordinary spherical enclosure R={R}, N={N}",
              qball(low) < value_j < qball(high))
print("flint version",flint.__version__,"Arb precision",ctx.prec)
print(f"ALL {passed} SONINE BESSEL COEFFICIENT / TAIL CHECKS PASSED")
