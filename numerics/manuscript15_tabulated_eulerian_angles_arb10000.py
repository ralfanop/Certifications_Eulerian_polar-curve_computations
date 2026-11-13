#!/usr/bin/env python3
"""Arb interval audit of the 13 *finite* Eulerian histogram angles in M15 Table 1.

Source: Manuscript 15, 13 Nov 2026, Table 1 and the definitions of
s_n and t_n in Section 2.4. Eulerian integer rows and 1/12-decimal-degree
references are independent: integers are exact and Arb encloses each angle.

This does NOT certify the n -> infinity angle limit, Gaussian asymptotics,
an all-odd-n strict bound, or reproduction of Figure 1's vector paths.
"""
from fractions import Fraction
from math import factorial

import flint
from flint import arb, ctx

WORK_BITS = 10000
REQUIRED_BITS = 8182
ctx.prec = WORK_BITS
assert ctx.prec == WORK_BITS

TABLE_DEGREES = {
    3: "53.130102354156",
    4: "115.641005824305",
    5: "53.130102354156",
    6: "112.773885489713",
    7: "54.432223114615",
    8: "111.581277371794",
    9: "56.203772691009",
    10: "111.094830381861",
    11: "58.120471153341",
    12: "110.958941929901",
    13: "60.054374987317",
    14: "111.015923260746",
    15: "61.951593918933",
}

HALF_LAST_DECIMAL = arb(1) / arb(2_000_000_000_000)
row = [1]  # n=1
minimum_bits = WORK_BITS
count = 0

print("M15 Eulerian apex angle table: independent finite Arb interval audit")
print("python-flint", flint.__version__, "Arb working bits", ctx.prec)

for n in range(2, 16):
    old = row
    row = [
        (k + 1) * (old[k] if k < len(old) else 0)
        + (n - k) * (old[k-1] if k else 0)
        for k in range(n)
    ]
    nfac = factorial(n)
    assert sum(row) == nfac, ("normalisation", n)
    assert all(v > 0 for v in row), ("positivity", n)
    assert row == row[::-1], ("symmetry", n)
    weights = [Fraction(v, nfac) for v in row]
    abscissae = [Fraction(k + 1, n + 1) for k in range(n)]
    mean = sum((w * x for w, x in zip(weights, abscissae)), Fraction(0))
    var = sum(
        (w * (x - Fraction(1, 2)) ** 2 for w, x in zip(weights, abscissae)),
        Fraction(0),
    )
    assert mean == Fraction(1, 2) and var == Fraction(1, 12 * (n + 1)), n
    if n < 3:
        continue

    if n % 2 == 1:
        m = (n - 1) // 2
        slope = Fraction((n + 1) * (row[m] - row[m - 1]), nfac)
        assert slope > 0, ("odd positive slope", n)
        angle_rad = arb(2) * (arb(slope.denominator) / arb(slope.numerator)).atan()
        if n in (3, 5):
            assert slope == 2, ("exceptional equal odd slopes", n)
        if n >= 7:
            assert slope < 2, ("finite strict odd bound", n)
    else:
        m = n // 2
        assert row[m - 1] == row[m], ("even central plateau", n)
        slope = Fraction((n + 1) * (row[m-1] - row[m-2]), nfac)
        assert slope > 0, ("even positive side slope", n)
        angle_rad = arb.pi() - (arb(slope.numerator) / arb(slope.denominator)).atan()

    degrees = angle_rad * arb(180) / arb.pi()
    bits = degrees.rel_accuracy_bits()
    assert degrees.is_finite() and bits >= REQUIRED_BITS, (n, bits)
    minimum_bits = min(minimum_bits, bits)
    reference = arb(TABLE_DEGREES[n])
    # Containment in the correct 12-decimal rounding cell, not just overlap.
    error = abs(degrees - reference)
    assert error < HALF_LAST_DECIMAL, ("12-place rounding failure", n, error)
    count += 1
    print(
        "n=", n, "exact slope=", slope, "table degrees=", TABLE_DEGREES[n],
        "angle interval=", degrees.str(46, radius=True, more=True),
        "certified relative bits=", bits,
    )

assert count == 13
print("SUCCESS: all 13 n=3..15 finite Eulerian angles enclosed within their")
print("12-decimal-degree rounding cells; min certified relative bits:",
      minimum_bits, "(required >=8182; working precision 10000).")
print("LIMIT STATUS: n->infinity and all-odd-n classification NOT established here.")
