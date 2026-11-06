#!/usr/bin/env python3
"""Manuscript 14.1, Theorem 4 (Sonine): rigorous Arb / exact rational checks.

Certificate scope:
- exact rational moment recurrence and finite binomial-integral evaluations;
- exact rational polynomial samples of H3*M=M*H2;
- coefficientwise J0/I0 -> spherical j0/sinhc tests;
- 2000-bit real/complex Arb enclosures at the Eulerian special parameter.

Finite sample checks and interval enclosures are not a proof of the
universal Sonine integral identity or entire-function interchange.
The corresponding formal coefficient intertwiner is proved in Lean.
"""
from fractions import Fraction as Q
from math import factorial, comb
from flint import arb, acb, ctx
import flint

ctx.prec = 2000
checks = 0

def check(label, proposition):
    global checks
    if not bool(proposition):
        raise AssertionError("FAIL: " + label)
    checks += 1
    print(f"PASS {checks:02d}: {label}")

def qball(q):
    q = Q(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

def moment(n):
    return Q(4**n * factorial(n)**2, factorial(2*n+1))

def moment_integral_poly(n):
    # (1/2) integral[-1,1] (1-u*u)^n du,
    # integrating the expanded finite binomial polynomial exactly.
    return sum((Q((-1)**k * comb(n,k), 2*k+1)
                for k in range(n+1)), Q(0))

def bessel_I0(n):
    return Q(1, 4**n * factorial(n)**2)

def bessel_J0(n):
    return (-1)**n * bessel_I0(n)

def spherical_modified(n):
    return Q(1, factorial(2*n+1))

def spherical_ordinary(n):
    return (-1)**n * spherical_modified(n)

def H2(a, n):
    return 4*(n+1)**2*a(n+1)

def H3(a, n):
    return 2*(n+1)*(2*n+3)*a(n+1)

def M(a, n):
    return moment(n)*a(n)

def sample(i):
    return lambda n: Q((n*n + 3*i*n - 7*i*i) % 31 - 15, (n+1)*(i+1))

print("python-flint", flint.__version__, "Arb precision", ctx.prec, "bits")

check("100 exact Sonine moment recurrences",
      all((2*n+3)*moment(n+1) == (2*n+2)*moment(n)
          for n in range(100)))
check("81 exact Sonine moments from integrated binomial polynomials",
      all(moment_integral_poly(n) == moment(n) for n in range(81)))
check("101 Sonine moments positive and normalized",
      moment(0) == 1 and all(moment(n) > 0 for n in range(101)))
check("129 coefficient identities H3 M = M H2, four rational profiles",
      all(H3(lambda k: M(sample(i), k), n)
          == M(lambda k: H2(sample(i), k), n)
          for n in range(129) for i in range(4)))
check("101 exact I0 -> spherical modified coefficients",
      all(moment(n)*bessel_I0(n) == spherical_modified(n)
          for n in range(101)))
check("101 exact J0 -> spherical ordinary coefficients",
      all(moment(n)*bessel_J0(n) == spherical_ordinary(n)
          for n in range(101)))

# At a=1/sqrt(8), sum of transformed I0 terms equals sinh(a)/a.
terms = lambda n: Q(1, 8**n * factorial(2*n+1))
N = 17
S = sum((terms(k) for k in range(N+1)), Q(0))
first_omitted = terms(N+1)
ratio = Q(1, 8*(2*N+4)*(2*N+5))
upper = S + first_omitted/(1-ratio)
check("exact strict geometric bound on the omitted positive tail",
      0 < ratio < 1 and S < upper)

a = arb(8).rsqrt()
valI = a.sinh()/a
check("Arb sinh(a)/a lies inside exact rational Taylor enclosure",
      qball(S) < valI < qball(upper))
check("Arb enclosure proves 50-decimal special-value interval",
      qball(Q("1.0209639298650195104786646351804211019462043266698")) < valI
      < qball(Q("1.0209639298650195104786646351804211019462043266700")))

# For sin(a)/a, successive partial sums of the alternating Taylor series
# give rigorous enclosing rationals since terms decrease for a^2=1/8.
S16 = sum(((-1)**k*terms(k) for k in range(17)), Q(0))
S17 = sum(((-1)**k*terms(k) for k in range(18)), Q(0))
valJ = a.sin()/a
check("alternating rational Taylor bounds are correctly ordered",
      S17 < S16 and S16-S17 == terms(17))
check("Arb sin(a)/a lies inside strict alternating bounds",
      qball(S17) < valJ < qball(S16))

z0 = acb(0, arb(2).rsqrt())
r = 2*(z0/2).sin()/z0
check("Arb Eulerian imaginary sinc matches Sonine I0 value below 1e-60",
      abs(r-acb(valI)) < qball(Q(1, 10**60)))
print("Arb modified spherical profile:", valI.str(65))
print("Arb ordinary spherical profile:", valJ.str(65))
print(f"ALL {checks} SONINE ARB/EXACT RATIONAL CHECKS PASSED")
