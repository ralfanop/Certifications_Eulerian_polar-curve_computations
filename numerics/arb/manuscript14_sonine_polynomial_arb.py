#!/usr/bin/env python3
"""Independent exact-Q and Arb checks of the polynomial Sonine integral.

Scope: finite-degree regression checks of the genuine real Sonine
averaging operator and its differential intertwiner; 256-bit Arb
special-value bounds. Global integral/entire identities are proved,
where available, by Lean, NOT by this finite test.
"""
from fractions import Fraction as Q
from math import factorial, comb
from flint import arb, acb, ctx
import flint

ctx.prec = 256
checks = 0

def check(label, prop):
    global checks
    if not bool(prop):
        raise AssertionError("FAIL: " + label)
    checks += 1
    print(f"PASS {checks:02d}: {label}")

def c(n):
    return Q(4**n * factorial(n)**2, factorial(2*n+1))

def c_from_integrated_polynomial(n):
    # (1/2)∫_-1^1 Σ_{k=0}^n (-1)^k C(n,k) u^(2k) du.
    return sum((Q((-1)**k * comb(n,k), 2*k+1)
                for k in range(n+1)), Q(0))

def coefs(seed, n):
    return Q((n*n + 13*n*(seed+1) - 7*seed) % 53 - 26,
             (n+seed+1)*(seed+2))

def lhs_integral_even_poly(seed, degree, t):
    # The integral is evaluated by independently integrating the
    # expanded monomial (1-u²)^n, with exact rational coefficients.
    return sum((coefs(seed,n)*t**(2*n)*c_from_integrated_polynomial(n)
                for n in range(degree+1)),Q(0))

def rhs_sonine_poly(seed, degree, t):
    return sum((coefs(seed,n)*c(n)*t**(2*n)
                for n in range(degree+1)),Q(0))

def radial3_of_M(seed, degree, t):
    return sum((coefs(seed,n) * 2*n*(2*n+1)*c(n)*t**(2*n-2)
                for n in range(1,degree+1)),Q(0))

def M_of_radial2(seed, degree, t):
    return sum((coefs(seed,n)*4*n*n*c(n-1)*t**(2*n-2)
                for n in range(1,degree+1)),Q(0))

def qb(q):
    return arb(str(q.numerator))/arb(str(q.denominator))

print("python-flint",flint.__version__,"precision",ctx.prec,"bits")

check("exact integrated Sonine moments 0..85",
      all(c_from_integrated_polynomial(n)==c(n) for n in range(86)))
check("finite real polynomials: 9 profiles x 5 rational t x 12 degrees",
      all(lhs_integral_even_poly(i,d,t)==rhs_sonine_poly(i,d,t)
          for i in range(9)
          for t in (Q(0),Q(1,7),Q(-3,5),Q(7,4),Q(-11,6))
          for d in (0,1,2,3,4,5,7,9,12,16,20,24)))
check("radial second-order intertwiner for same finite profiles",
      all(radial3_of_M(i,d,t)==M_of_radial2(i,d,t)
          for i in range(9)
          for t in (Q(0),Q(1,7),Q(-3,5),Q(7,4),Q(-11,6))
          for d in (0,1,2,3,4,5,7,9,12,16,20,24)))
check("exact zero-origin second-order radial limit for all profiles",
      all(radial3_of_M(i,24,Q(0))==M_of_radial2(i,24,Q(0))
          for i in range(9)))

# N=20 Taylor polynomials of the real spherical profiles at a=1/sqrt(8),
# with a rigorous positive-tail bound.
N=20
qterms=lambda n: Q(1,8**n*factorial(2*n+1))
SP=sum((qterms(n) for n in range(N+1)),Q(0))
ratio=Q(1,8*(2*N+4)*(2*N+5))
UP=SP+qterms(N+1)/(1-ratio)
a=arb(8).rsqrt()
val=a.sinh()/a
check("strict exact positive remainder of 21-term spherical modified profile",
      0<ratio<1 and SP<UP and qb(SP)<val<qb(UP))
SN=sum(((-1)**n*qterms(n) for n in range(N+1)),Q(0))
SN1=SN-qterms(N+1)
ordinary=a.sin()/a
check("strict alternating remainder of 21-term spherical ordinary profile",
      SN1<SN and qb(SN1)<ordinary<qb(SN))
z=acb(0,arb(2).rsqrt())
sinc=2*(z/2).sin()/z
check("complex Arb Eulerian imaginary sinc matches spherical profile <1e-60",
      abs(sinc-acb(val))<qb(Q(1,10**60)))
print("Arb Eulerian spherical modified profile:",val.str(65))
print("Arb spherical ordinary profile:",ordinary.str(65))
print(f"ALL {checks} NEW SONINE POLYNOMIAL ARB/EXACT CHECKS PASSED")
