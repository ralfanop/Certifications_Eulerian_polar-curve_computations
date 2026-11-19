"""Exact rational finite-composition residual audit for M14 (225).

For t=x^2, let E=sum_{j=1}^{12} t^j/(2j+1)! and N=6E/t-1.
This checks the entire composed finite polynomials, not sampled values.
On |t|<=1 their residuals are bounded by the sum of absolute tail
coefficients.  This is not a Lean kernel check of the analytic substitution.
"""
from fractions import Fraction as Q
from math import factorial


def mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i+j] += u*v
    return out


def log_poly(y, n):
    out = [Q(0)] * (n*(len(y)-1)+1)
    power = [Q(1)]
    for k in range(1, n+1):
        power = mul(power, y)
        for i, p in enumerate(power):
            out[i] += (-1)**(k+1)*p/k
    return out


# Exact coefficients from Manuscript14.ParryResidual.a and .c (#371).
A = list(map(Q, ['1/6','-1/180','1/2835','-1/37800','1/467775',
    '-691/3831077250','2/127702575','-3617/2605132530000',
    '43867/350813659321125','-174611/15313294652906250',
    '155366/147926426347074375','-236364091/2423034863565078262500']))
C = list(map(Q, ['0','1/20','-1/16800','-1/756000',
    '89/3104640000','-1579/4540536000000','5069/2288430144000000',
    '1013/64838854080000000','-133302011/182129747556556800000000',
    '230510617/18440636940101376000000000',
    '-106522465321/857694513680715110400000000000',
    '42162599/233916685549285939200000000000']))


def main():
    E = [Q(0)] + [Q(1, factorial(2*j+1)) for j in range(1, 13)]
    N = [6*p for p in E[1:]]
    N[0] -= 1
    assert E[0] == N[0] == 0
    assert sum(abs(p) for p in E) < Q(1, 4)
    assert sum(abs(p) for p in N) < Q(1, 16)
    den = log_poly(E, 12)
    num = log_poly(N, 11)
    assert den[:13] == [Q(0)] + A
    assert num[:12] == C
    den_tail = sum(abs(p) for p in den[13:])
    num_tail = sum(abs(p) for p in num[12:])
    # Exact, intentionally inexpensive majorants, not floating estimates.
    assert den_tail < Q(1, 1000)
    assert num_tail < Q(1, 1000)
    print('PASS: exact first 12 coefficients in both composed polynomials')
    print(f'PASS: full denominator residual ({len(den)-13} coefficients), l1 < 1/1000')
    print(f'PASS: full numerator residual ({len(num)-12} coefficients), l1 < 1/1000')
    print('Hence |logPoly12(E(t))-t*A12(t)| <= |t|^13/1000,')
    print('and |logPoly11(N(t))-C12(t)| <= |t|^12/1000 for |t|<=1.')


if __name__ == '__main__':
    main()
