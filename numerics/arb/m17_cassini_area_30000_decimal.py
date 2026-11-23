#!/usr/bin/env python3
"""Rigorous independent FLINT/Arb 30,000-place upgrade of M17 Cassini values.

Source: user's 2026-11-23 Manuscript_17_20261123_REFERENCES_REPAIRED_FINAL(1).zip,
Cyclohedral.tex, theorem m17-curvature-area, eqs. m17-area, m17-area-integration:
  L8(1,chi2) = log(1+sqrt(2))/sqrt(2)
  Area_lobe = pi * (1-L8(1,chi2))

The two transcendental closed-form values are enclosed using Arb outward-rounded
balls. Exact DYADIC rational endpoints strictly fit a single nearest-10^-30000
rounding cell for EACH value. The ball is not converted via float or decimal
before checking. This certifies the printed DECIMALS of those closed forms;
it does NOT prove the Dirichlet-series identity or geometric area theorem.

This also computes the artanh closed-form as a separate Arb expression and
requires agreement of all 30,000 rounded decimal places.
"""
import hashlib
import json
import sys
from pathlib import Path

import flint
from flint import arb, ctx, fmpz

WORK_BITS = 120000
MIN_REL_BITS = 110000
PLACES = 30000
assert flint.__version__ == "0.9.0"
ctx.prec = WORK_BITS
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
SCALE = fmpz(10) ** PLACES


def rigorously_rounded_decimal(name, x):
    assert x.is_finite() and x > 0, (name, "not a positive finite enclosure")
    acc = x.rel_accuracy_bits()
    assert acc >= MIN_REL_BITS, (name, "insufficient verified bits", acc)
    lower = x.lower().fmpq()
    upper = x.upper().fmpq()
    assert 0 < lower <= upper, (name, "invalid enclosure endpoints")

    # nearest integer to 10^PLACES * x, determined by the strict rounding
    # cell for *both* exact rational Arb interval endpoints.
    n = (2 * lower.p * SCALE + lower.q) // (2 * lower.q)
    assert 2 * lower.p * SCALE > (2 * n - 1) * lower.q, (
        name, "lower endpoint crosses a half-ulp boundary")
    assert 2 * upper.p * SCALE < (2 * n + 1) * upper.q, (
        name, "upper endpoint crosses a half-ulp boundary")
    assert (n - 1) * lower.q < lower.p * SCALE, (
        name, "sanity: nearest decimal lower")
    assert upper.p * SCALE < (n + 1) * upper.q, (
        name, "sanity: nearest decimal upper")

    whole = n // SCALE
    fraction = str(n % SCALE).zfill(PLACES)
    assert len(fraction) == PLACES
    digits = str(whole) + "." + fraction

    # Store exact dyadic enclosure and the Arb-native decimal ball.
    return {
        "name": name,
        "working_bits": WORK_BITS,
        "relative_accuracy_bits": acc,
        "decimal_places": PLACES,
        "rounded_decimal": digits,
        "rounded_sha256": hashlib.sha256(digits.encode("ascii")).hexdigest(),
        "strict_half_ulp_rounding_cell": True,
        "arb_ball": x.str(PLACES + 80, radius=True, more=True),
        "lower_endpoint_exact": str(lower),
        "upper_endpoint_exact": str(upper),
    }


def main():
    sqrt2 = arb(2).sqrt()
    pi = arb.pi()
    l8 = (arb(1) + sqrt2).log() / sqrt2
    area = pi * (arb(1) - l8)

    # Independent evaluation of the alternative artanh expression from
    # Eq. (m17-area-integration); equality follows from the elementary
    # logarithm identity, not from numerical agreement alone.
    artanh = ((sqrt2 + 1) / (sqrt2 - 1)).log() / 2
    l8_alt = artanh / sqrt2
    area_alt = pi * (arb(1) - l8_alt)

    data = [
        rigorously_rounded_decimal("L8(1,chi2) closed form", l8),
        rigorously_rounded_decimal("Cassini critical lobe area", area),
    ]
    l8_second = rigorously_rounded_decimal("L8 alternative artanh", l8_alt)
    area_second = rigorously_rounded_decimal("Area alternative artanh", area_alt)
    assert l8_second["rounded_decimal"] == data[0]["rounded_decimal"], (
        "30k-digit disagreement in L8")
    assert area_second["rounded_decimal"] == data[1]["rounded_decimal"], (
        "30k-digit disagreement in area")

    # Alternative evaluations must have intersecting, outward-rounded balls.
    assert not (l8 < l8_alt or l8 > l8_alt), "L8 intervals are disjoint"
    assert not (area < area_alt or area > area_alt), "Area intervals are disjoint"

    result = {
        "status": "CERTIFIED",
        "precision_definition": "30,000 digits AFTER decimal point",
        "backend": "FLINT/Arb via python-flint " + flint.__version__,
        "working_bits": WORK_BITS,
        "required_min_relative_accuracy_bits": MIN_REL_BITS,
        "source": "M17 Eq. m17-area; Eq. m17-area-integration; 2026-11-23 REFERENCES_REPAIRED_FINAL",
        "mathematical_scope": "Closed-form numerical values only; not a proof of metric integration or L-series identity",
        "crosscheck": "second independently evaluated artanh expression; 30,000 decimal places agree",
        "values": data,
    }
    target = Path("m17-cassini-area-arb-30000-decimal-certificate.json")
    target.write_text(json.dumps(result, ensure_ascii=True, indent=2), encoding="utf-8")
    for d in data:
        print("CERTIFIED", d["name"], "30,000 decimal places;",
              "verified relative bits:", d["relative_accuracy_bits"],
              "rounded SHA256:", d["rounded_sha256"], flush=True)
    print("SUCCESS M17 ARB 30000 EXACT DECIMAL PLACES", flush=True)


if __name__ == "__main__":
    main()
