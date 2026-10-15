#!/usr/bin/env python3
"""Exact (integer / rational) checks linking Hermite polynomials and the
type-B Catalan numbers C(2k,k).  Standard library only.

(A) H_{2n}(0) = (-1)^n C(2n,n) n!            (physicists' Hermite, n <= NMAX)
    from the recurrence H_{n+1}(0) = -2n H_{n-1}(0), H_0 = 1, H_1(0) = 0.

(B) Hermite coefficients of sign(x).  With He_n the probabilists' Hermite
    polynomials and X ~ N(0,1), put c_n = E[sign(X) He_n(X)] / sqrt(n!).
    Since d/dx[He_{n-1}(x) phi(x)] = -He_n(x) phi(x) (phi the N(0,1) density),
        E[sign(X) He_{2k+1}(X)] = 2 phi(0) He_{2k}(0) = 2 (-1)^k (2k-1)!! / sqrt(2 pi),
    hence  c_{2k+1}^2 = (2/pi) ((2k-1)!!)^2 / (2k+1)!,  c_{2k} = 0.
    We check exactly that ((2k-1)!!)^2/(2k+1)! = C(2k,k) / (4^k (2k+1)).
    Consequently Grothendieck's identity reads
        (2/pi) arcsin(rho) = sum_k c_{2k+1}^2 rho^{2k+1}
                           = (2/pi) sum_k C(2k,k) rho^{2k+1} / (4^k (2k+1)),
    and the Krivine constant log(1+sqrt2) = arcsinh(1)
                           = sum_k (-1)^k C(2k,k) / (4^k (2k+1)).

(C) Haagerup's complex function: the integral
        int_0^{pi/2} cos^2(t) sin^{2k}(t) dt = (pi/2) C(2k,k) / (4^k (2k+2)),
    checked exactly through the Wallis ratio (2k-1)!!/(2k+2)!!, gives
        phi_C(t) = t int_0^{pi/2} cos^2 / sqrt(1 - t^2 sin^2)
                 = (pi/4) sum_k C(2k,k) C_k t^{2k+1} / 16^k,   C_k = C(2k,k)/(k+1).
"""
from fractions import Fraction as Fr
from math import comb, factorial

NMAX = 200


def dfact(m):                       # double factorial, (-1)!! = 1
    r = 1
    while m > 1:
        r *= m
        m -= 2
    return r


# (A)
H = [1, 0]                          # H_0(0), H_1(0)
for n in range(1, 2 * NMAX):
    H.append(-2 * n * H[n - 1])
for n in range(NMAX + 1):
    assert H[2 * n] == (-1) ** n * comb(2 * n, n) * factorial(n), n
print(f"(A) H_2n(0) = (-1)^n C(2n,n) n!   verified exactly for n = 0..{NMAX}")

# (B)
for k in range(NMAX + 1):
    lhs = Fr(dfact(2 * k - 1) ** 2, factorial(2 * k + 1))
    rhs = Fr(comb(2 * k, k), 4 ** k * (2 * k + 1))
    assert lhs == rhs, k
print(f"(B) ((2k-1)!!)^2/(2k+1)! = C(2k,k)/(4^k(2k+1))   verified exactly for k = 0..{NMAX}")
print("    c_{2k+1}^2 = (2/pi) C(2k,k)/(4^k(2k+1)); first values of (pi/2) c_{2k+1}^2:",
      [str(Fr(comb(2 * k, k), 4 ** k * (2 * k + 1))) for k in range(6)])

# (C)  Wallis: int_0^{pi/2} sin^{2k} cos^2 = (pi/2) (2k-1)!! / (2k+2)!!
for k in range(NMAX + 1):
    wallis = Fr(dfact(2 * k - 1), dfact(2 * k + 2))
    assert wallis == Fr(comb(2 * k, k), 4 ** k * (2 * k + 2)), k
    # coefficient of t^{2k+1}:  (C(2k,k)/4^k) * (pi/2) * C(2k,k)/(4^k (2k+2))
    coef = Fr(comb(2 * k, k), 4 ** k) * Fr(1, 2) * Fr(comb(2 * k, k), 4 ** k * (2 * k + 2))
    catalan = Fr(comb(2 * k, k), k + 1)
    assert coef == Fr(1, 4) * comb(2 * k, k) * catalan / 16 ** k, k   # (pi factored out)
print(f"(C) phi_C(t) = (pi/4) sum C(2k,k) C_k t^(2k+1)/16^k: coefficients verified exactly for k = 0..{NMAX}")
print("ALL EXACT CHECKS PASSED")
