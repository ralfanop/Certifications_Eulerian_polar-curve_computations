#!/usr/bin/env python3
"""Exact checks of the scalar steps of Saha et al. Sections 9.5 and 10 (lower bound 6 pi / 11), in rationals.

 (a) low range:   2 r_-^2 + pi/2 < 11/6,  r_- = (1 - 1/sqrt3)/2,  i.e.  2/3 - 1/sqrt3 + pi/2 < 11/6
 (b) middle range: x^2 - x + 1/6 <= 0 on [r_-, r_+]  (r_+- are its roots: algebra)
 (c) high range:  (3x-2)^2 - (6x^2 - 6x + 1) = 3(1-x)^2 (polynomial identity) and 3 r_+ - 2 > 0
 (d) Prop. 10.2:  2 (11/12)^3 > 1, and the identity
        11/(12 b) + 2 (b - 11/12)(11/12)^3 / b^4 = 1 + (b - 11/12)(2 (11/12)^3 - b^3) / b^4
"""
from fractions import Fraction as F
pi_lo, pi_hi = F(314159265358979323846, 10**20), F(314159265358979323847, 10**20)
# 1/sqrt3 in [s_lo, s_hi]
from math import isqrt
N = 10**30
s_lo = F(isqrt(N * N // 3), N); s_hi = s_lo + F(1, N)
assert s_lo * s_lo * 3 <= 1 <= s_hi * s_hi * 3
ok = True
a = F(2, 3) - s_lo + pi_hi / 2
print(f"(a) 2/3 - 1/sqrt3 + pi/2 <= {float(a):.12f} < 11/6 = {float(F(11,6)):.12f}: {a < F(11,6)}"); ok &= a < F(11, 6)
# (b),(c) symbolic identities checked on many rationals (polynomials of degree <= 4: 6 points suffice)
for x in [F(k, 7) for k in range(-3, 10)]:
    assert (3*x - 2)**2 - (6*x*x - 6*x + 1) == 3*(1 - x)**2
    b = x + 2
    lhs = F(11, 12) / b + 2 * (b - F(11, 12)) * F(11, 12)**3 / b**4
    rhs = 1 + (b - F(11, 12)) * (2 * F(11, 12)**3 - b**3) / b**4
    assert lhs == rhs
rp_lo = (1 + s_lo) / 2
print(f"(c) 3 r_+ - 2 >= {float(3*rp_lo - 2):.6f} > 0: {3*rp_lo - 2 > 0}; identity (3x-2)^2 - (6x^2-6x+1) = 3(1-x)^2: True"); ok &= 3*rp_lo - 2 > 0
print(f"(b) r_+- = (1 +- 1/sqrt3)/2 are the roots of x^2 - x + 1/6: product = 1/6, sum = 1 (algebra)")
d = 2 * F(11, 12)**3
print(f"(d) 2 (11/12)^3 = {d} = {float(d):.6f} > 1: {d > 1}; Prop. 10.2 identity: True"); ok &= d > 1
print("ALL SCALAR CHECKS PASSED" if ok else "FAILED")
