"""Remark 3.15 of the V478 manuscript: two-term asymptotic of c_n and the corrected crossing order.

c_n = n! / ((n+1) * (E(n,(n-1)/2) - E(n,(n-3)/2)))  for odd n >= 3  (E(n,k) in Deza's convention).
The manuscript states, by Laplace's method applied to the Fourier inversion of Eq. (78),
    c_n = sqrt(pi (n+1)/216) * (1 + 15/(4(n+1)) + O(n^-2)),
so the crossing c_n = pi (alpha_n = theta_E) moves from n+1 ~ 216 pi to n+1 ~ 216 pi - 15/2.

This script (i) computes c_n exactly (rational arithmetic, exact Eulerian recurrence) for odd n <= 1001
and prints (n+1)(c_n / sqrt(pi(n+1)/216) - 1), which should tend to 15/4 = 3.75;
(ii) checks 670 < 216 pi - 15/2 < 672 and 216 pi > 672 with both interval backends (mpmath.iv and
ia_fixed) and, independently, with the rational bounds 333/106 < pi < 355/113 used in Eq. (80)
(also proved in Lean: EulerianCert.Crossing).

Part (i) is a numerical corroboration of the analytic expansion, not a proof of it.
"""
from fractions import Fraction
from math import factorial
import mpmath as mp

mp.mp.dps = 50
NMAX = 1001

def eulerian_rows(nmax):
    row = [1]                      # n = 1: E(1,0) = 1
    yield 1, row
    for m in range(1, nmax):       # E(m+1,k) = (k+1) E(m,k) + (m+1-k) E(m,k-1)
        row = [(k + 1) * (row[k] if k < len(row) else 0) + (m + 1 - k) * (row[k - 1] if k >= 1 else 0)
               for k in range(m + 1)]
        yield m + 1, row

c = {}
for n, row in eulerian_rows(NMAX):
    assert sum(row) == factorial(n)
    if n % 2 == 1 and n >= 3:
        c[n] = Fraction(factorial(n), (n + 1) * (row[(n - 1) // 2] - row[(n - 3) // 2]))

print("(i) scaled second-order coefficient (n+1)(c_n/sqrt(pi(n+1)/216) - 1), expected limit 15/4:")
prev = None
mono = True
for n in sorted(c):
    lead = mp.sqrt(mp.pi * (n + 1) / 216)
    beta = (n + 1) * (mp.mpf(c[n].numerator) / c[n].denominator / lead - 1)
    if n >= 101:
        if prev is not None and not beta < prev:
            mono = False
        prev = beta
    if n in (5, 21, 101, 301, 501, 669, 671, 801, 1001):
        print(f"  n = {n:5d}:  c_n = {mp.nstr(mp.mpf(c[n].numerator) / c[n].denominator, 15):>18}"
              f"   (n+1)(ratio-1) = {mp.nstr(beta, 12)}")
print("  strictly decreasing in n for odd 101 <= n <= 1001:", mono, "; last value - 15/4 =",
      mp.nstr(prev - mp.mpf(15) / 4, 6))

print("(ii) corrected crossing order 216 pi - 15/2:")
iv = mp.iv
iv.dps = 50
x = 216 * iv.pi - iv.mpf(15) / 2
print("  interval enclosure:", x, "  670 < . < 672:", bool(x.a > 670 and x.b < 672))
lo, hi = 216 * Fraction(333, 106) - Fraction(15, 2), 216 * Fraction(355, 113) - Fraction(15, 2)
print(f"  from 333/106 < pi < 355/113: {float(lo):.6f} < 216 pi - 15/2 < {float(hi):.6f};"
      f" 670 < lo and hi < 672: {lo > 670 and hi < 672}")
print("  one-term estimate 216 pi > 672 (outside the bracket):", bool((216 * iv.pi).a > 672))

import ia_fixed as fx                  # independent backend: exact integers, no mpmath
y = fx.FI.frac(216) * fx.PI - fx.FI.frac(Fraction(15, 2))
ylo, yhi = Fraction(y.lo, 1 << fx.P), Fraction(y.hi, 1 << fx.P)
z = fx.FI.frac(216) * fx.PI
print(f"  ia_fixed: width {float(yhi - ylo):.1e}; 670 < . < 672: {ylo > 670 and yhi < 672};"
      f" 216 pi > 672: {Fraction(z.lo, 1 << fx.P) > 672}")
