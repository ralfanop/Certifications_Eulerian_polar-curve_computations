#!/usr/bin/env python3
"""Manuscript 14.1 §7: exact finite determinant / Arb enclosure audit.

Universal finite product positivity and monotonicity: Lean 4.
Exact rational polynomial logarithmic-derivative tests: finite cases only.
Arb tests: 2000-bit validated ball inequalities comparing Euler-product
truncations with sinh(x)/x at the two Eulerian points.
The infinite-dimensional Fredholm/zeta identity is NOT certified here.
"""
from fractions import Fraction as Q
from flint import arb, ctx
import flint

ctx.prec = 2000
checks = 0

def check(label, condition):
    global checks
    if not bool(condition):
        raise AssertionError("FAIL: " + label)
    checks += 1
    print("PASS %02d: %s" % (checks, label))

def polynomial_coefficients(N):
    a = [Q(1)]
    for n in range(1, N + 1):
        q = Q(1, n*n)
        b = [Q(0)] * (len(a)+1)
        for i, c in enumerate(a):
            b[i] += c
            b[i+1] += c*q
        a = b
    return a

def value(coeffs, x):
    return sum((c*x**n for n,c in enumerate(coeffs)), Q(0))

def derivative_value(coeffs, x):
    return sum((n*c*x**(n-1) for n,c in enumerate(coeffs) if n), Q(0))

NQ = 65
p = polynomial_coefficients(NQ)
check("exact degree and normalization, N=65",
      len(p) == NQ+1 and p[0] == 1 and all(c>0 for c in p))
for x in [Q(1,9), Q(1,8), Q(1,2), Q(4,3)]:
    lhs = derivative_value(p,x)
    rhs = value(p,x)*sum((1/(Q(n*n)+x) for n in range(1,NQ+1)),Q(0))
    check("finite log-derivative identity at rational t=%s" % x, lhs == rhs)
check("finite product strict monotonicity, N=65",
      value(p,Q(1,8)) < value(p,Q(1,2)))

PI = arb.pi()
def arb_product(N, x2):
    u = x2/(PI*PI)
    d = arb(1)
    for n in range(1, N+1):
        d *= 1 + u/(n*n)
    return d, d*(u/N).exp()

def test_point(label, x2):
    a = x2.sqrt()
    target = a.sinh()/a
    lower, upper = arb_product(500,x2)
    check(label+" strict Arb Euler-product enclosure (500 factors)",
          lower < target < upper)
    # 1/N is a rigorous analytic upper bound on sum_{n>N} 1/n^2;
    # the numerical balls on both sides are outward rounded.
    print(label, "sinh(x)/x:", target.str(65))
    print(label, "finite determinant:", lower.str(42))

test_point("z0, x^2=1/8", arb(1)/8)
test_point("z1, x^2=1/2", arb(1)/2)
# Finite spectral resolvent and squared-HS traces at both special shifts.
# Rigorous analytic tail estimates from the integral comparison:
# 0 < R-R_N < 1/(pi^2 N), 0 < Q-Q_N < 1/(3 pi^4 N^3).
def trace_bounds(N, x2):
    R = arb(0)
    Q = arb(0)
    for n in range(1, N+1):
        den = PI*PI*n*n + x2
        R += 1/den
        Q += 1/(den*den)
    return R, R + 1/(PI*PI*N), Q, Q + 1/(3*PI**4*N**3)

def check_trace(label, x2):
    a = x2.sqrt()
    sinh = a.sinh()
    trace_exact = (a.cosh()/sinh)/(2*a) - 1/(2*x2)
    var = 1/x2 - 1/(sinh*sinh)
    squared_exact = (2*trace_exact-var)/(4*x2)
    lo, hi, slo, shi = trace_bounds(500, x2)
    check(label+" 500-term shifted resolvent trace Arb enclosure",
          lo < trace_exact < hi)
    check(label+" 500-term squared resolvent trace Arb enclosure",
          slo < squared_exact < shi)
    print(label, "trace =", trace_exact.str(65))
    print(label, "trace of squared resolvent =", squared_exact.str(65))

check_trace("z0, shift 1/8", arb(1)/8)
check_trace("z1, shift 1/2", arb(1)/2)

check("positive parameter and exact reciprocal-ratio relation", (arb(1)/8)*4 == arb(1)/2)
print("python-flint", flint.__version__, "Arb precision", ctx.prec, "bits")
print("ALL %d FINITE DIRICHLET ARB/RATIONAL CHECKS PASSED" % checks)
