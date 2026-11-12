#!/usr/bin/env python3
"""Manuscript 15, Fig. 1: exact Eulerian histograms n=3,...,7002.

Each unnormalised E(n,j) is calculated as an exact Python integer:
 E(1,0)=1; E(n,j)=(j+1)E(n-1,j)+(n-j)E(n-1,j-1).
The total mass n! is checked by *exact integers* for every n.

All 7000 central peak probabilities are enclosed by Arb at 10000
working bits and required to have >=8182 certified relative bits.
This certifies the mathematical Eulerian probabilities, not the
five-decimal-pt quantisation of the manually rendered vector paths.
"""
import math
from flint import arb, ctx

N_MAX = 7002
SAMPLES = {3, 60, 670, 671, 1000, 2000, 5000, 7002}
WORK_PREC = 10000
ACCURACY = 8182
ctx.prec = WORK_PREC
assert ctx.prec == WORK_PREC

row = [1]   # n=1
factorial = 1
sample_count = 0
certified_count = 0
min_certified_bits = WORK_PREC
for n in range(2, N_MAX + 1):
    next_row = [1] * n
    for j in range(1, n - 1):
        next_row[j] = (j + 1) * row[j] + (n - j) * row[j - 1]
    row = next_row
    factorial *= n
    if n >= 3:
        assert sum(row) == factorial, ("normalization", n)
        assert all(v > 0 for v in row), ("positivity", n)
        assert row[0] == row[-1] == 1, ("endpoints", n)
        # Exact reflection symmetry from the arithmetic recursion:
        assert all(row[j] == row[n - 1 - j] for j in range(n // 2)), ("symmetry", n)
    if n >= 3:
        centre = (n - 1) // 2
        peak_num = row[centre]
        assert peak_num == max(row), ("peak", n)
        # Certify EVERY one of the 7000 central probabilities, not only
        # the eight samples printed for human-readable inspection.
        peak = arb(peak_num) / arb(factorial)
        assert peak.is_finite(), ("nonfinite ball", n)
        bits = peak.rel_accuracy_bits()
        assert bits >= ACCURACY, ("insufficient enclosure accuracy", n, bits)
        min_certified_bits = min(min_certified_bits, bits)
        certified_count += 1
        if n in SAMPLES:
            print("n=", n, "peak_index=", centre + 1,
                  "E(n, peak-1) bit length=", peak_num.bit_length(),
                  "n! bit length=", factorial.bit_length())
            print("  peak probability =", peak.str(82, radius=True, more=True))
            print("  certified relative accuracy =", bits, "bits")
            sample_count += 1

assert sample_count == len(SAMPLES), sample_count
assert certified_count == 7000, certified_count
assert n == N_MAX
print("EXACT: normalization, positivity and symmetry checked for every n=3,...,7002")
print(f"SUCCESS — all 7000 Eulerian central peak probabilities certified at 10000 working bits; minimum {min_certified_bits} relative bits (threshold {ACCURACY})")
