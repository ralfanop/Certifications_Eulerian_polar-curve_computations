#!/usr/bin/env python3
"""Manuscript 14.1: Arb certification for Corollary 3.6 ONLY.

256-bit Arb enclosures and exact-Q finite regression checks.
The universal identities are Lean theorems, not finite numerical tests.
"""
from fractions import Fraction as Q
from math import factorial
import sys
from flint import arb, acb, ctx
import flint

ctx.prec = 256
checks = 0

def check(label, assertion):
    global checks
    if not bool(assertion):
        raise AssertionError('FAIL: ' + label)
    checks += 1
    print(f'PASS {checks:02d}: {label}')

def qball(q):
    q = Q(q)
    return arb(str(q.numerator)) / arb(str(q.denominator))

def a(n):
    return Q(4**n * factorial(n)**2, factorial(2*n + 1))

def b(n):
    return Q(4**n, factorial(2*n + 1))

def B2(seq, n):
    return seq(n) / factorial(n)**2

def LA(seq, n):
    if n == 0:
        return Q(1,2) * seq(0)
    return (Q(n) + Q(1,2))*seq(n) - n*seq(n-1)

def LF(seq, n):
    if n == 0:
        return Q(0)
    return n*(Q(n)+Q(1,2))*seq(n) - seq(n-1)

def theta(seq, n):
    return n*seq(n)

def T(seq, n):
    return Q(-1,16)**n * seq(n)

def D(seq, n):
    if n == 0:
        return Q(0)
    return (2*n)*(2*n+1)*seq(n) + Q(1,4)*seq(n-1)

print(f'python-flint={flint.__version__}, Arb precision={ctx.prec} bits')
N = 64
check('64 even coefficients of DT=4TL_F (exact Q)',
      all(D(lambda k: T(b,k), n) == 4*T(lambda k: LF(b,k), n)
          for n in range(N)))
check('64 coefficients of DT B2=4Ttheta B2 L_A (exact Q)',
      all(D(lambda k: T(lambda j: B2(a,j), k), n)
          == 4*T(lambda j: theta(lambda k: B2(lambda m: LA(a,m),k),j),n)
          for n in range(N)))
check('64 coefficients: L_F(B2A)=0 (exact Q)',
      all(LF(lambda k: B2(a,k),n) == 0 for n in range(N)))
check('64 coefficients: D(TB2A)=0 (exact Q)',
      all(D(lambda k: T(lambda j: B2(a,j),k),n) == 0 for n in range(N)))

M = 14
terms = lambda n: Q(1,8**n * factorial(2*n + 1))
S = sum((terms(n) for n in range(M+1)), Q(0))
first_omitted = terms(M+1)
q = Q(1,8*(2*M+4)*(2*M+5))
UP = S + first_omitted/(1-q)
check('exact positive geometric-tail enclosure', 0 < q < 1 and S < UP)

alpha = arb(8).rsqrt()
value = alpha.sinh()/alpha
check('Arb value inside exact rational-series enclosure',
      qball(S) < value < qball(UP))
check('Arb value within 48-decimal interval',
      qball(Q('1.0209639298650195104786646351804211019462043266698')) < value <
      qball(Q('1.0209639298650195104786646351804211019462043266700')))

z = acb(0,arb(2).rsqrt())
r = 2*(z/2).sin()/z
rp = (z/2).cos()/z - 2*(z/2).sin()/z**2
rpp = -(z/2).sin()/(2*z) - 2*(z/2).cos()/z**2 + 4*(z/2).sin()/z**3
res = z**2*rpp + 2*z*rp + z**2*r/4
check('Arb r_E(z0) agrees with real-valued enclosure to 1e-60',
      abs(r-acb(value)) < qball(Q(1,10**60)))
check('Arb D_(1/2) r_E(z0) residual below 1e-60',
      abs(res) < qball(Q(1,10**60)))
print('r_E(i/sqrt(2)) Arb enclosure:',value.str(64))
print('D_(1/2)r_E(z0) Arb residual:',res)
print(f'ALL {checks} COROLLARY 3.6 ARB/RATIONAL CHECKS PASSED')
sys.exit(0)
