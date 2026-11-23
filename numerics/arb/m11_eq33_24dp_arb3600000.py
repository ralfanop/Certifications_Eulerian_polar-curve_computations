#!/usr/bin/env python3
"""M11 Eq. (33) 24-place angle certificate: exact rounding cell + Arb 3.6M bits.

Source: author's uploaded Manuscript_11_20261121_OEIS(1).zip, 11/11.tex.
Eq. (28) has 24 fractional decimal digits. Eq. (33) is the EXACT
geometric identity theta_E = 2 arccot(pi), expressed in degrees.

No new mathematical identity, theorem or Lean dependency is claimed.
The Arb ball encloses the exact value computed via real atan and pi.
All interval endpoint comparisons are STRICT; no float is used.
The independent million_decimal_common checker also checks the complete
1,000,001-significant-digit exact rounding cell using rational/dyadic
outward interval endpoints, and archives the ball and rounded digits.
"""
from fractions import Fraction as Q
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, exact, record, finish

PRINTED = "35.313574302825716957635467"
DECIMAL_PLACES = 24

def main():
    assert ctx.prec == WORK == 3_600_000
    assert MIN == 3_400_000 and DIGITS == 1_000_001
    assert len(PRINTED.split(".")[1]) == DECIMAL_PLACES

    pi = arb.pi()
    theta_deg = arb(360) * (arb(1) / pi).atan() / pi
    assert theta_deg.is_finite()
    assert theta_deg.rel_accuracy_bits() >= MIN
    assert theta_deg > 0

    centre = Q(PRINTED)
    half_unit = Q(1, 2 * 10**DECIMAL_PLACES)
    lower = exact(centre - half_unit)
    upper = exact(centre + half_unit)
    # Because the comparison is between rigorous outward-rounded Arb
    # balls, these imply both exact strict rational inequalities:
    # (2d-10^-24)/2 < theta_deg < (2d+10^-24)/2.
    assert lower < theta_deg < upper, (
        "FAIL: printed M11 Eq. (33) not rigorously rounded to 24 places",
        theta_deg.str(60, radius=True, more=True))
    print("M11 Eq. (33): theta_E = 2 arccot(pi) degrees", flush=True)
    print("Rounded 24 places:", PRINTED, flush=True)
    print("Strict exact rational rounding cell: PASS", flush=True)
    print("Working bits:", ctx.prec,
          "verified relative bits:", theta_deg.rel_accuracy_bits(), flush=True)

    record("M11 Eq (33) theta_E in degrees", theta_deg)
    finish("m11eq33")
    print("SUCCESS M11 EQ33 24DP ARB3600000", flush=True)

if __name__ == "__main__":
    main()
