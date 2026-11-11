#!/usr/bin/env python3
"""Manuscript 15, Eqs. (34)-(37): 10000-bit Arb enclosure of the
inverse-central-binomial series with a mathematically rigorous tail.

Series S = sum_{k>=0} (4/5)^k / [(2k+1) * binom(2k,k)].

For t_0=1 the exact recurrence is
    t_{k+1} = t_k * 2*(k+1)/(5*(2*k+3)).
All t_k are positive and, by exact integer inequality
2*(k+1) < 2*k+3, each ratio is strictly less than 1/5.
Thus 0 < sum_{k=N}^infty t_k < (5/4)*t_N.
The argument is independent of Arb's floating-point calculations.

The interval hull of the outward-rounded partial sum and the partial
sum plus an outward-rounded upper tail bound rigorously encloses S.
"""
import flint
from flint import arb, ctx

PRECISION = 10000
MIN_CERTIFIED_REL_BITS = 8182
N = 4000
ctx.prec = PRECISION
assert ctx.prec == PRECISION
one, two, four, five = [arb(k) for k in (1, 2, 4, 5)]

term = one
partial = arb(0)
for k in range(N):
    assert 2 * (k + 1) < (2 * k + 3), (k, "geometric ratio proof failed")
    partial += term
    term = term * arb(2 * (k + 1)) / arb(5 * (2 * k + 3))

# t_N is enclosed by term; the exact tail is <= (5/4) t_N.
tail_bound = (five / four) * term
assert tail_bound.is_finite()
assert tail_bound.lower() > 0
series = partial.union(partial + tail_bound.upper())
assert series.rel_accuracy_bits() >= MIN_CERTIFIED_REL_BITS

# The following are certified enclosure results for the infinite series.
# The analytical identity to arctan(1/2) comes from the beta-integral
# argument in the manuscript, NOT from numerical interval overlap.
atan_from_series = (two / five) * series
alpha_from_series = (four / five) * series
plouffe_from_series = (two / (five * arb.pi())) * series
pi = arb.pi()
degrees_from_series = (arb(180) / pi) * alpha_from_series

records = {
    "inverse-binomial infinite sum S": series,
    "atan(1/2) via inverse-binomial series": atan_from_series,
    "alpha_3 via inverse-binomial series": alpha_from_series,
    "p_gamma via inverse-binomial series": plouffe_from_series,
    "alpha_3 degrees via inverse-binomial series": degrees_from_series,
}
for name, value in records.items():
    bits = value.rel_accuracy_bits()
    print(name, value.str(65, radius=True, more=True))
    print("  certified relative accuracy:", bits, "bits")
    assert bits >= MIN_CERTIFIED_REL_BITS, (name, bits)

# Independent, non-proof consistency overlap with direct Arb arctan.
angle_direct = (one / two).atan()
assert atan_from_series.overlaps(angle_direct)
assert alpha_from_series.overlaps(two * angle_direct)
assert plouffe_from_series.overlaps(angle_direct / pi)

# Independent strict check of the manuscript's ten-decimal-degree label.
printed_degrees = arb(531301023542) / arb(10**10)
half_ulp = one / arb(2 * 10**10)
assert abs(degrees_from_series - printed_degrees) < half_ulp

print("TAIL CERTIFIED by exact ratio bound: 0 < remainder < (5/4) t_4000")
print("FIGURE 1 CERTIFIED independently: alpha_3 rounds to 53.1301023542 degrees")
print("SUCCESS — five inverse-binomial series enclosures with >=8182 certified bits at 10000 working bits")
