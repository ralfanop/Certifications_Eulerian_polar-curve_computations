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
# Exact Gaussian rationals x + i y with Fractions.
class Q:
    def __init__(s, re, im=0): s.re, s.im = Fr(re), Fr(im)
    def __add__(s, o): o = o if isinstance(o, Q) else Q(o); return Q(s.re+o.re, s.im+o.im)
    def __sub__(s, o): o = o if isinstance(o, Q) else Q(o); return Q(s.re-o.re, s.im-o.im)
    def __mul__(s, o): o = o if isinstance(o, Q) else Q(o); return Q(s.re*o.re-s.im*o.im, s.re*o.im+s.im*o.re)
    def __truediv__(s, o):
        o = o if isinstance(o, Q) else Q(o); n = o.re*o.re+o.im*o.im
        return Q((s.re*o.re+s.im*o.im)/n, (s.im*o.re-s.re*o.im)/n)
    def __eq__(s, o): o = o if isinstance(o, Q) else Q(o); return s.re == o.re and s.im == o.im
    def __repr__(s): return f"{s.re}" if s.im == 0 else f"({s.re}{'+' if s.im >= 0 else '-'}{abs(s.im)}i)"


def const_term(delta, eps, a, b):
    # coefficient of y_xi after division by b^2 is  eps/b^2 * xi + (delta - eps a/b)/b
    return (Q(delta) - Q(eps)*a/b)/b


# Principal square roots, chosen exactly with eps = +-2k^2:
#   eps = -2k^2 < 0: sqrt(-eps/2) = k,   sqrt(-1/(2eps)) = 1/(2k)          (real)
#   eps = +2k^2 > 0: sqrt(-eps/2) = i k, sqrt(-1/(2eps)) = i/(2k)         (imaginary)
for sign in (-1, +1):
    for k in (1, 2, 3):
        eps = Fr(sign*2*k*k)
        b = Q(k) if sign < 0 else Q(0, k)
        s = Q(Fr(1, 2*k)) if sign < 0 else Q(0, Fr(1, 2*k))
        assert b*b == Q(-eps/2) and s*s == Q(-1/(2*eps))
        assert Q(eps)/(b*b) == Q(-2)                          # slope -2: Hermite form
        for delta in (Fr(1), Fr(3), Fr(-5, 7)):
            c_printed = const_term(delta, eps, Q(delta)*s, b)  # Bochner's xi, principal roots
            c_other = const_term(delta, eps, Q(-delta)*s, b)
            if sign > 0:
                assert c_printed == 0
            else:
                assert c_other == 0 and c_printed == Q(2*delta)/b
            print(f"eps={eps}, delta={delta}: sqrt(-eps/2)={b}, sqrt(-1/(2eps))={s};"
                  f"  constant with Bochner's xi = {c_printed}")
print("Bochner's xi = delta sqrt(-1/(2eps)) + sqrt(-eps/2) x with principal roots gives the")
print("Hermite form exactly when eps > 0 (complex xi; for eps = 1 both coefficients equal")
print("z0 = i/sqrt2 = sqrt(-1/2), so xi = z0 (delta + x)); for eps < 0 (real xi) the roots")
print("need opposite signs, xi = -delta sqrt(-1/(2eps)) + sqrt(-eps/2) x.")
print("ALL CHECKS PASSED")
