#!/usr/bin/env python3
"""
tail_close.py -- exact rational closing step of the near-linearity criterion

    gamma + sum_{3 <= m <= N} |b_m| + sum_{m > N} |b_m| < b_1          (Saha et al. Prop. 6.1; Peng Lemma 2.2)

with the tail bounded by Cauchy-Schwarz and Parseval on the unit circle,

    sum_{m > N, m odd} |b_m| <= ||D^3 H||_{L2(T)} (sum_{m > N, m odd} m^-6)^{1/2} <= B3 / sqrt(10 N^5),
    B3^2 = ||D^3 H||^2 <= C_a (J_0 + a J_1),   C_a = sum_{n >= 0} 1/(1 + a n^2) = 1/2 + pi/(2 sqrt a) coth(pi/sqrt a),

where J_0, J_1 are the upper bounds of d3norm (inner domain + analytic exterior).  For a = s^2 with s rational,
C_a <= 1/2 + pi_hi/(2 s) (1 + 2/(2z + 2z^2)),  z = pi_lo/s  (e^{2z} - 1 >= 2z + 2z^2).
Every comparison is an exact Fraction comparison.

usage: tail_close.py N gamma head_up b1_lo J0_up J1_up [s ...]      (decimal strings; gamma may be 'peng')
"""
import sys
from fractions import Fraction as F

pi_lo, pi_hi = F(314159265358979323846, 10**20), F(314159265358979323847, 10**20)

def isqrt_up(x):
    """rational upper bound of sqrt(x) for a Fraction x > 0 (Newton step from above)"""
    from math import isqrt
    s = 10**30
    n, d = x.numerator, x.denominator
    r = F(isqrt(n * s * s // d) + 1, s)
    while r * r < x:
        r += F(1, s)
    return r

def main():
    N = int(sys.argv[1])
    gamma = F(sys.argv[2]) if sys.argv[2] != 'peng' else pi_hi * 5000 / 17813      # gamma <= 5000 pi_hi / 17813
    head, b1 = F(sys.argv[3]), F(sys.argv[4])
    J0, J1 = F(sys.argv[5]), F(sys.argv[6])
    ss = [F(x) for x in sys.argv[7:]] or [F(1, 8), F(1, 4), F(1, 2), F(1), F(2)]
    room = b1 - gamma - head
    print(f"N = {N}, gamma <= {float(gamma):.12f}, head <= {float(head):.6e}, b1 >= {float(b1):.15f}")
    print(f"room for the tail: b1 - gamma - head >= {float(room):.6e}")
    best = None
    for s in ss:
        a = s * s
        z = pi_lo / s
        Ca = F(1, 2) + pi_hi / (2 * s) * (1 + 2 / (2 * z + 2 * z * z))
        B3sq = Ca * (J0 + a * J1)
        # tail <= sqrt(B3sq / (10 N^5))
        T = isqrt_up(B3sq / (10 * F(N) ** 5))
        ok = T < room
        print(f"  a = {float(a):.6g}: C_a <= {float(Ca):.6f}, B3^2 <= {float(B3sq):.6f}, tail <= {float(T):.6e}  {'< room: OK' if ok else 'not enough'}")
        if ok and (best is None or T < best[1]):
            best = (a, T)
    if best:
        a, T = best
        print(f"CERTIFIED: gamma + sum_{{m>=3}} |b_m| < b1 with margin >= {float(room - T):.6e} (a = {float(a):.6g})")
        return 0
    print("NOT certified with these J bounds")
    return 1

if __name__ == '__main__':
    sys.exit(main())
