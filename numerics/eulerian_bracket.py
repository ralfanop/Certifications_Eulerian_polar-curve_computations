"""Exact-integer check of Remark 3.16 / Eq. (91) of the V478 manuscript (crossing order)
and the scan of all odd orders up to 1001.

E(n,k), 0<=k<=n-1 (Deza's convention, as in Sec. 2 of the manuscript): permutations of [n] with
exactly k ascents.  row[k] below is E(n,k).  With p_{n,k} = E(n,k-1)/n! (Eq. 76),
c_n = 1/s_n = n! / ((n+1) * (E(n,(n-1)/2) - E(n,(n-3)/2)))   for odd n >= 3.
"""
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60
NMAX = 1001

def eulerian_rows(nmax):
    row = [1]  # n = 1: E(1,0) = 1
    # recurrence E(n,k) = (k+1) E(n-1,k) + (n-k) E(n-1,k-1), written with 1-based list positions
    yield 1, row
    for n in range(2, nmax + 1):
        new = [0] * n
        for k in range(1, n + 1):
            a = k * row[k - 1] if k - 1 < len(row) else 0
            b = (n - k + 1) * row[k - 2] if k >= 2 else 0
            new[k - 1] = a + b
        row = new
        yield n, row

fact = 1
cs = {}
for n, row in eulerian_rows(NMAX):
    fact *= n
    assert sum(row) == fact
    assert row == row[::-1]
    if n % 2 == 1 and n >= 3:
        kc = (n + 1) // 2
        diff = row[kc - 1] - row[kc - 2]
        cs[n] = Fraction(fact, (n + 1) * diff)
    if n in (669, 670, 671):
        globals()[f"row{n}"] = row
        globals()[f"fact{n}"] = fact

c669, c671 = cs[669], cs[671]
print("c_669 =", mp.nstr(mp.mpf(c669.numerator) / c669.denominator, 40))
print("c_671 =", mp.nstr(mp.mpf(c671.numerator) / c671.denominator, 40))
print("c_669 < 333/106 :", c669 < Fraction(333, 106))
print("355/113 < c_671 :", Fraction(355, 113) < c671)
def trunc(x, dec):
    d = Fraction(dec); k = len(dec.split(".")[1])
    return d <= x < d + Fraction(1, 10**k)
print("Eq. (91) printed c_669 = 3.13914926973... certified:", trunc(c669, "3.13914926973"))
print("Eq. (91) printed c_671 = 3.14377888960... certified:", trunc(c671, "3.14377888960"))
# monotonicity of c_n over odd n and the unique crossing of pi
odd = sorted(cs)
print("c_3 = c_5 = 1/2:", cs[3] == cs[5] == Fraction(1, 2))
odd5 = [n for n in odd if n >= 5]
mono = all(cs[a] < cs[b] for a, b in zip(odd5, odd5[1:]))
print("c_n strictly increasing for odd 5..%d:" % NMAX, mono)
cross = [n for n in odd[:-1] if mp.mpf(cs[n].numerator) / cs[n].denominator < mp.pi < mp.mpf(cs[n + 2].numerator) / cs[n + 2].denominator]
print("odd n with c_n < pi < c_{n+2}:", cross)
# leading asymptotics c_n ~ sqrt(pi*(n+1)/216)
for n in (101, 301, 669, 671, 1001):
    v = mp.mpf(cs[n].numerator) / cs[n].denominator
    print(n, mp.nstr(v, 15), "sqrt(pi D/216)=", mp.nstr(mp.sqrt(mp.pi * (n + 1) / 216), 15))
# number of decimal digits of the integers involved
print("digits of 671!:", len(str(fact671)))
