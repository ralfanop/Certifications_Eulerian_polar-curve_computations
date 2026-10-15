#!/usr/bin/env python3
"""Exact-arithmetic check of two formulas on p. 733 of
S. Bochner, Ueber Sturm-Liouvillesche Polynomsysteme, Math. Z. 29 (1929) 730-736
(GDZ copy PPN002370980, page 738 of the volume PDF).

(A) The printed Hermite sum
      P_n(x) = sum_{r=0}^{[n/2]} (-1)^r C(2r,r) C(n,2r) (2x)^(n-2r)
    is compared with H_n(x) = sum_r (-1)^r n!/(r!(n-2r)!) (2x)^(n-2r),
    and both are inserted in y'' - 2x y' + 2n y = 0.
    The identity n!/(r!(n-2r)!) = C(2r,r) C(n,2r) r! is checked term by term.

(B) The transformation of Normalform 2, y'' + (delta + eps x) y' + lam y = 0,
    by xi = a + b x with b = sqrt(-eps/2):
    the y_xi coefficient after division by b^2 is (delta + eps x)/b with
    x = (xi - a)/b, i.e.  eps/b^2 * xi + (delta - eps a / b)/b.
    Hermite form needs constant term 0, i.e. a = delta*b/eps = -delta/sqrt(-2 eps).
    Printed: a = +delta*sqrt(-1/(2 eps)) = +delta/sqrt(-2 eps).
    Checked on exact rational instances with eps = -2 k^2 (so b = k is rational).

Only Python's standard library (integers and Fractions) is used.
"""
from fractions import Fraction as Fr
from math import comb, factorial

NMAX = 20


def printed(n):
    return {n - 2*r: (-1)**r * comb(2*r, r) * comb(n, 2*r) * 2**(n - 2*r)
            for r in range(n//2 + 1)}


def hermite(n):
    return {n - 2*r: (-1)**r * factorial(n) // (factorial(r) * factorial(n - 2*r)) * 2**(n - 2*r)
            for r in range(n//2 + 1)}


def residual(p, n):
    """Coefficients of y'' - 2 x y' + 2 n y for y = sum p[k] x^k."""
    res = {}
    for k, c in p.items():
        if k >= 2:
            res[k-2] = res.get(k-2, 0) + k*(k-1)*c
        res[k] = res.get(k, 0) + (2*n - 2*k)*c
    return {k: v for k, v in res.items() if v}


def fmt(p):
    return " ".join(f"{c:+d}x^{k}" for k, c in sorted(p.items(), reverse=True))


print("(A) Hermite sum on p. 733")
first_bad = None
for n in range(NMAX + 1):
    P, H = printed(n), hermite(n)
    rP, rH = residual(P, n), residual(H, n)
    assert not rH, (n, rH)                      # H_n solves the Hermite equation
    for r in range(n//2 + 1):                   # identity with the missing r!
        assert factorial(n) // (factorial(r)*factorial(n-2*r)) == comb(2*r, r)*comb(n, 2*r)*factorial(r)
    same = (P == H)
    if not same and first_bad is None:
        first_bad = n
    assert same == (n <= 3)
    print(f"n={n:2d} printed==H_n: {same!s:5}  ODE residual(printed): {'0' if not rP else fmt(rP)}")
    if n in (4, 5):
        print(f"       printed: {fmt(P)}")
        print(f"       H_n    : {fmt(H)}")
print(f"first n where the printed sum differs from H_n and fails the ODE: {first_bad}")
print("identity n!/(r!(n-2r)!) = C(2r,r) C(n,2r) r!  verified for all n <= %d" % NMAX)

print()
print("(B) Transformation of Normalform 2 on p. 733")


def const_term(delta, eps, a, b):
    # y_xi coefficient / b^2 :  (delta + eps*(xi - a)/b)/b  -> constant part
    return (delta - eps*a/b) / b


def slope(eps, b):
    return eps / b**2


for k in (1, 2, 3):
    eps = Fr(-2*k*k)
    b = Fr(k)                                   # sqrt(-eps/2)
    s = Fr(1, 2*k)                              # sqrt(-1/(2 eps)) = 1/sqrt(-2 eps)
    assert b*b == -eps/2 and s*s == -1/(2*eps)
    for delta in (Fr(1), Fr(3), Fr(-5, 7)):
        assert slope(eps, b) == -2
        printed_c = const_term(delta, eps, +delta*s, b)
        correct_c = const_term(delta, eps, -delta*s, b)
        assert correct_c == 0 and printed_c == 2*delta/b == 4*delta*s
        print(f"eps={eps}, delta={delta}: y'' coeff of y_xi = -2 xi + c;"
              f"  c(printed a=+delta s) = {printed_c},  c(a=-delta s) = {correct_c}")
print("printed sign leaves -2 xi + 2 delta/b = -2 (xi - 2a), a shifted equation (not Hermite form unless delta = 0);"
      " xi = -delta sqrt(-1/(2eps)) + sqrt(-eps/2) x gives the Hermite form.")
print("ALL CHECKS PASSED")
