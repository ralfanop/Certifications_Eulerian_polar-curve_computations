#!/usr/bin/env python3
"""Check the exact finite Eulerian rows, 12-decimal central angles, and the weak limit.

For odd n: alpha = 2 atan(1/s), s = (n+1)(E(n,m)-E(n,m-1))/n!.
For even n: alpha = pi-atan(t), t = (n+1)(E(n,m-1)-E(n,m-2))/n!.
The discrete probability measure mu_n supported at k/(n+1), k=1..n,
has mean 1/2 and variance 1/[12(n+1)] and converges weakly to delta_1/2.
"""
from fractions import Fraction
from math import factorial
from decimal import Decimal, ROUND_HALF_UP
import mpmath as mp
mp.mp.dps=80
row=[1]
for n in range(2,18):
    old=row
    row=[(k+1)*(old[k] if k<len(old) else 0) +
         (n-k)*(old[k-1] if k else 0) for k in range(n)]
    assert len(row)==n
    assert row==row[::-1], 'symmetry'
    assert sum(row)==factorial(n), 'mass'
    k=[Fraction(j+1,n+1) for j in range(n)]
    avg=sum(Fraction(c,factorial(n))*x for c,x in zip(row,k))
    var=sum(Fraction(c,factorial(n))*(x-Fraction(1,2))**2 for c,x in zip(row,k))
    assert avg==Fraction(1,2) and var==Fraction(1,12*(n+1)), 'moment formulas'
    if n<3:continue
    if n%2:
        m=(n-1)//2
        slope=Fraction((n+1)*(row[m]-row[m-1]),factorial(n))
        angle=2*mp.atan(mp.mpf(slope.denominator)/slope.numerator)
    else:
        m=n//2
        slope=Fraction((n+1)*(row[m-1]-row[m-2]),factorial(n))
        angle=mp.pi-mp.atan(mp.mpf(slope.numerator)/slope.denominator)
    angle_s=str(Decimal(mp.nstr(mp.degrees(angle),70)).quantize(
        Decimal('0.000000000001'),rounding=ROUND_HALF_UP))
    print(f'{n:2d}: {angle_s} degrees')
print('n -> infinity: mu_n converges weakly to delta_(1/2); alpha_n -> 180 degrees.')
