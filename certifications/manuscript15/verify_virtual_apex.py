"""Exact finite comparisons for the virtual Eulerian apex theorem.

Run `python verify_virtual_apex.py` for integer-only checks.
Run with `--arb` under python-flint for the optional high-precision enclosure.
The uniform analytic estimate for n >= 72 is proved in the manuscript.
"""

import argparse
from fractions import Fraction
from math import factorial


def verify():
    row = [1]
    slopes = {}
    for n in range(2, 71):
        def entry(k):
            return row[k] if 0 <= k < len(row) else 0

        row = [(k + 1) * entry(k) + (n - k) * entry(k - 1)
               for k in range(n)]
        assert sum(row) == factorial(n)
        assert row == row[::-1]
        if n < 4 or n % 2:
            continue
        m = n // 2
        slopes[n] = Fraction((n + 1) * (row[m - 1] - row[m - 2]),
                             factorial(n))

    peak = Fraction(9473633, 3628800)
    assert slopes[12] == peak > 2
    assert all(t < peak for n, t in slopes.items() if n != 12)
    assert [n for n, t in slopes.items() if t > 2] == list(range(4, 50, 2))
    assert all(t < 2 for n, t in slopes.items() if n >= 50)
    assert all(t > 0 for t in slopes.values())
    # Rational estimates replacing the two analytic tail terms for N >= 73.
    assert Fraction(288, 73) < Fraction(199, 100) ** 2
    assert Fraction(8 * 73, 72 * 3**73) < Fraction(1, 100)
    print(f"PASS: {len(slopes)} finite even orders; unique maximum n=12: {peak}")
    print("PASS: t_n > 2 exactly for even n=4,...,48 in the checked range")
    print("PASS: rational constants in the uniform analytic tail bound")
    return peak


def atan_bounds(q, count=128):
    """Alternating-series bounds for 0 < q < 1, exact rational arithmetic."""
    assert 0 < q < 1 and count % 2 == 0
    lower = sum(((-1) ** k * q ** (2 * k + 1) / (2 * k + 1)
                 for k in range(count)), Fraction(0))
    upper = lower + q ** (2 * count + 1) / (2 * count + 1)
    return lower, upper


def certify_decimal(peak):
    lo, hi = atan_bounds(1 / peak)
    lo5, hi5 = atan_bounds(Fraction(1, 5))
    lo239, hi239 = atan_bounds(Fraction(1, 239))
    # Machin's identity for pi.
    pi_lo = 16 * lo5 - 4 * hi239
    pi_hi = 16 * hi5 - 4 * lo239
    deg_lo, deg_hi = 360 * lo / pi_hi, 360 * hi / pi_lo
    assert 0 < pi_lo < pi_hi
    scale = 10**50
    digits = 4191788385980154510779093799569188384742770659567188
    assert digits <= scale * deg_lo < scale * deg_hi < digits + 1
    assert Fraction(digits) - Fraction(1, 2) < scale * deg_lo
    assert scale * deg_hi < Fraction(digits) + Fraction(1, 2)
    print("PASS: exact rational 50-place truncation and rounding of 41.91788385980154510779093799569188384742770659567188 degrees")


def certify_arb(peak, bits):
    from flint import arb, ctx

    ctx.prec = bits
    rad = 2 * (arb(peak.denominator) / arb(peak.numerator)).atan()
    deg = 180 * rad / arb.pi()
    reference = 2 * (arb(1) / 2).atan()
    assert deg > 0 and rad < reference
    for name, value in [("radians", rad), ("degrees", deg)]:
        accuracy = value.rel_accuracy_bits()
        assert accuracy >= 3_400_000, (name, accuracy)
        print(f"PASS Arb {name}: {accuracy} relative accuracy bits")
        print(value.str(45))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--arb", action="store_true")
    parser.add_argument("--bits", type=int, default=3_600_000)
    args = parser.parse_args()
    p = verify()
    certify_decimal(p)
    if args.arb:
        certify_arb(p, args.bits)
