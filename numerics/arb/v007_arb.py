#!/usr/bin/env python3
"""Certificates for the numerical statements of manuscript V007 (Eulerian Fourier profiles and
Gegenbauer--Fock operators).  Exact rational arithmetic (Python Fractions) and Arb ball arithmetic
(python-flint); every comparison is either exact or a certain Arb comparison.

1. Prop. 6.5: the fifteen-term partial sum S_15 of I = sum_n 1/(4^n n! (2n+1)) (Eq. 56), the
   remainder bound (Eq. 57) with e^(1/4) < 4/3, and the decimal enclosure (Eq. 55); independently,
   Arb encloses I = (1/2) int_{-1}^{1} e^(u^2/4) du = sqrt(pi) erfi(1/2) inside (55).
2. Table 1: A_d(k) k^(d-2) = 4 Gamma(d/2) (4 pi)^((d-2)/2) for d = 3..12, and the endpoint values
   2k (d = 1) and 4 (d = 2), as exact rational multiples of powers of pi; Cor. 4.2: 8 pi.
3. Prop. 6.6 at alpha = 1 (consistency of Eq. 58 with Eq. 59 of the proof): the series
   sum_k 1/(16^k (2k)! (2k+1)^2) and 4 Shi(1/4) agree in Arb.
"""
from fractions import Fraction as Q
from math import factorial
import sys

import flint
from flint import arb, ctx

ctx.prec = 256
ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= bool(ok)
    print(f"{name:72s} {'CERTIFIED' if ok else 'FAIL'}")


def ex(q):
    q = Q(q)
    return arb(str(q.numerator)) / q.denominator


print(f"python {sys.version.split()[0]}; python-flint {flint.__version__}; {ctx.prec} bits\n")

# ---------------------------------------------------------------- 1. Prop. 6.5
term = lambda n: Q(1, 4 ** n * factorial(n) * (2 * n + 1))
S15 = sum(term(n) for n in range(15))
report("Eq. (56): S_15 = 337212679483569969430703669/309376751206532288348160000",
       S15 == Q(337212679483569969430703669, 309376751206532288348160000))
R = Q(4, 3) / (4 ** 15 * factorial(15))
report("Eq. (57): (4/3)/(4^15 15!) = 1/1053078495820775424000", R == Q(1, 1053078495820775424000))
# e^(1/4) < 4/3: sum_j 4^-j/j! < 1 + (1/4) sum_j 4^-j = 4/3 term by term (j! >= 1, strict from j = 2)
E = arb(1) / 4
report("Eq. (57): e^(1/4) < 4/3 (Arb)", bool(E.exp() < ex(Q(4, 3))))
# remainder: sum_{n>=15} term(n) <= sum_{j>=0} 1/(4^(15+j) 15! j!) = e^(1/4)/(4^15 15!) < R
lo, hi = Q("1.089974208367244447324816"), Q("1.089974208367244447325767")
report("Eq. (55), exact: lo < S_15 and S_15 + R < hi", lo < S15 and S15 + R < hi)
I_erfi = arb.pi().sqrt() * (arb(1) / 2).erfi()
# independent series enclosure: 60 terms plus the same tail majorant (now with 60 in place of 15)
S60 = sum(term(n) for n in range(60))
I_ser = arb(ex(S60), ex(Q(4, 3) / (4 ** 60 * factorial(60))).upper())
report("Eq. (54)-(55), Arb: sqrt(pi) erfi(1/2) lies strictly inside (55)",
       bool(I_erfi > ex(lo)) and bool(I_erfi < ex(hi)))
report("Eq. (54), Arb: sqrt(pi) erfi(1/2) and the series enclosure overlap",
       I_erfi.overlaps(I_ser))
print(f"{'':6s}I = {I_erfi.str(30)}")
print(f"{'':6s}width of the printed enclosure (55): {float(hi - lo):.3e}\n")

# ---------------------------------------------------------------- 2. Table 1 and Cor. 4.2
# A_d(k) k^(d-2) = 4 Gamma(d/2) (4 pi)^((d-2)/2).  Exact form: (rational) * pi^p.
def gamma_half(d):
    """Gamma(d/2) as (rational, power of pi): pi^(1/2) for odd d is recorded as 1/2."""
    if d % 2 == 0:
        return Q(factorial(d // 2 - 1)), Q(0)
    r = Q(1)                      # Gamma(1/2) = pi^(1/2)
    x = Q(1, 2)
    while x < Q(d, 2):
        r *= x
        x += 1
    return r, Q(1, 2)


printed = {3: (4, 1), 4: (16, 1), 5: (24, 2), 6: (128, 2), 7: (240, 3), 8: (1536, 3),
           9: (3360, 4), 10: (24576, 4), 11: (60480, 5), 12: (491520, 5)}
good = True
for d, (coef, p) in printed.items():
    g, gp = gamma_half(d)
    rat = 4 * g * Q(4) ** Q(d - 2, 2) if d % 2 == 0 else 4 * g * 2 ** (d - 2)
    pw = gp + Q(d - 2, 2)
    good &= (rat == coef and pw == p)
    # Arb cross-check of the closed form at k = 1
    A = 4 * arb(d / 2 if d % 2 == 0 else ex(Q(d, 2))).gamma() * (4 * arb.pi()) ** (ex(Q(d - 2, 2)))
    good &= bool(A.overlaps(coef * arb.pi() ** p))
report("Table 1, d = 3..12: A_d(k) = 4 Gamma(d/2)(2 sqrt(pi)/k)^(d-2) as printed", good)
# endpoints: d = 1: 4 Gamma(1/2) (4 pi)^(-1/2) k = 2k; d = 2: 4
report("Table 1, d = 1, 2: 2k and 4", 4 * Q(1) / 2 == 2 and 4 * 1 == 4)
c3 = 4 * ex(Q(1, 2)) * arb.pi().sqrt() * (2 * arb.pi().sqrt() / ex(Q(1, 2)))
report("Cor. 4.2: 4 Gamma(3/2)(2 sqrt(pi)/(1/2)) = 8 pi (Arb)", c3.overlaps(8 * arb.pi()))
print()

# ---------------------------------------------------------------- 3. Prop. 6.6 at alpha = 1
ser = sum(Q(1, 16 ** k * factorial(2 * k) * (2 * k + 1) ** 2) for k in range(40))
ser_ball = arb(ex(ser), ex(Q(1, 16 ** 40 * factorial(80))).upper() * 2)
shi = 4 * (arb(1) / 4).shi()
report("Prop. 6.6, alpha = 1: sum_k 1/(16^k (2k)!(2k+1)^2) = 4 Shi(1/4) (Arb overlap)", shi.overlaps(ser_ball))
print(f"{'':6s}||r_E||_1^2 = {shi.str(30)}\n")

print("ALL CERTIFIED" if ok_all else "SOME CHECK FAILED")
sys.exit(0 if ok_all else 1)
