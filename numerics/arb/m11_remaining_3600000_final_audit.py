#!/usr/bin/env python3
"""Manuscript 11: fail-closed, exact 20,000-fractional-place audit.

Only verifies supplied rational enclosures and their recombination;
mathematical provenance of source intervals requires pinned CI execution.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

# Decimal conversion of 20,000 digits exceeds CPython's default 4,300-digit limit.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

PLACES = 20_000
MIN_REL_BITS = 66_439
WORK_BITS = 80_000
PRINTED_DK = "0.203783759536049443826081"


def endpoint(obj):
    n, d = int(obj["numerator"]), int(obj["denominator"])
    if d <= 0:
        raise ValueError("invalid exact rational denominator")
    return Fraction(n, d)


def interval(manifest, key):
    obj = manifest[key]
    lo, hi = endpoint(obj["lower"]), endpoint(obj["upper"])
    if not 0 < lo <= hi:
        raise ValueError("invalid positive exact enclosure: " + key)
    return lo, hi


def same_decimal_cell(lo, hi, places=PLACES):
    """Exact nearest-even rounding cell, with both boundaries STRICT."""
    if not 0 < lo <= hi:
        raise ValueError("rounding needs a positive ordered interval")
    scale = 10 ** places

    def nearest_even(x):
        num, den = x.numerator * scale, x.denominator
        q, r = divmod(num, den)
        return q + int(2 * r > den or (2 * r == den and q % 2 == 1))

    k = nearest_even(lo)
    if nearest_even(hi) != k:
        raise ValueError("endpoint decimal rounding cells disagree")
    lower, upper = Fraction(2 * k - 1, 2 * scale), Fraction(2 * k + 1, 2 * scale)
    if not (lower < lo <= hi < upper):
        raise ValueError("enclosure touches a decimal rounding boundary")
    return k


def exact_decimal(k, places=PLACES):
    digits = str(k).zfill(places + 1)
    return digits[:-places] + "." + digits[-places:]


def check_bits(lo, hi, name):
    # Exact rational interval comparison, independently checked using Arb.
    from flint import arb, ctx, fmpq, fmpz
    ctx.prec = WORK_BITS
    l = fmpq(fmpz(lo.numerator), fmpz(lo.denominator))
    h = fmpq(fmpz(hi.numerator), fmpz(hi.denominator))
    ball = arb((l + h) / 2, arb((h - l) / 2).upper())
    if not (ball.lower().fmpq() <= l and h <= ball.upper().fmpq()):
        raise ValueError(name + ": reconstructed Arb ball lost an endpoint")
    bits = ball.rel_accuracy_bits()
    if bits < MIN_REL_BITS:
        raise ValueError(f"{name}: {bits} actual relative bits < {MIN_REL_BITS}")
    return bits


def verify_length(m, panels):
    n = int(m.get("panels", 0))
    if m.get("index") is not None or n < 32 or len(panels) != n:
        raise ValueError("full length requires every independent panel manifest")
    if int(m.get("working_bits", 0)) < MIN_REL_BITS:
        raise ValueError("insufficient length working precision")
    combined_lo, combined_hi = interval(m, "enclosure")
    lo, hi, seen = Fraction(0), Fraction(0), set()
    for pm in panels:
        idx = pm.get("index")
        if not isinstance(idx, int) or idx in seen or not (0 <= idx < n):
            raise ValueError("duplicate or invalid length panel index")
        if any(pm.get(k) != m.get(k) for k in ("working_bits", "threshold_bits", "panels")):
            raise ValueError("length panel precision/parameter mismatch")
        seen.add(idx)
        a, b = interval(pm, "enclosure")
        lo += a
        hi += b
    if seen != set(range(n)):
        raise ValueError("missing length panel")
    if not (combined_lo <= lo <= hi <= combined_hi):
        raise ValueError("combined length interval does not enclose exact sum of panels")
    if not (Fraction("5.5510") < combined_lo <= combined_hi < Fraction("5.5511")):
        raise ValueError("published length prefix inconsistent")
    return combined_lo, combined_hi


def verify_curvature(m):
    if m.get("quantity") != "D_kappa, Eq. (50)":
        raise ValueError("wrong curvature quantity")
    params = m.get("parameters", {})
    n = params.get("panels")
    if not isinstance(n, int) or n < 32 or n % 2:
        raise ValueError("invalid curvature panel count")
    if int(params.get("bits", 0)) < MIN_REL_BITS:
        raise ValueError("insufficient curvature working precision")
    halves = m.get("halves", [])
    if len(halves) != 2 or sorted(h.get("direction") for h in halves) != [-1, 1]:
        raise ValueError("both independently integrated curvature halves required")
    if any(not isinstance(h.get("orders"), list) or len(h["orders"]) != n // 2 or
           any(not isinstance(o, int) or o <= 0 for o in h["orders"]) for h in halves):
        raise ValueError("missing or incomplete curvature Taylor orders")
    integrals = [interval(h, "integral") for h in halves]
    a, b = (sum(pair[i] for pair in integrals) for i in (0, 1))
    lo, hi = interval(m, "discrepancy")
    # D_kappa = sqrt(I_left + I_right): exact necessary enclosure conditions.
    if not (lo * lo <= a <= b <= hi * hi):
        raise ValueError("D_kappa enclosure does not enclose sqrt of both half-integrals")
    scale = 10 ** 24
    printed = Fraction(PRINTED_DK)
    if not (printed - Fraction(1, 2 * scale) < lo <= hi < printed + Fraction(1, 2 * scale)):
        raise ValueError("published 24-place curvature cell mismatch")
    return lo, hi


def load(path):
    data = Path(path).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--length-manifest", required=True)
    p.add_argument("--length-panel-manifests", nargs="+", required=True)
    p.add_argument("--curvature-manifest", required=True)
    p.add_argument("--expected-head-sha", required=True)
    p.add_argument("--output", default="m11-certified-20000-decimals.json")
    args = p.parse_args()
    sha = args.expected_head_sha
    if len(sha) != 40 or any(c not in "0123456789abcdef" for c in sha):
        raise ValueError("full lowercase source HEAD SHA required")

    length, length_hash = load(args.length_manifest)
    curvature, curvature_hash = load(args.curvature_manifest)
    panels_and_hashes = [load(path) for path in args.length_panel_manifests]
    if length.get("head_sha") != sha or curvature.get("head_sha") != sha:
        raise ValueError("one or both complete manifest HEAD SHA tags are missing or mismatched")
    outputs = {}
    for name, m, validator, source_hash in (
        ("length", length, lambda m: verify_length(m, [x[0] for x in panels_and_hashes]), length_hash),
        ("curvature", curvature, verify_curvature, curvature_hash),
    ):
        lo, hi = validator(m)
        bits = check_bits(lo, hi, name)
        decimal = exact_decimal(same_decimal_cell(lo, hi))
        outputs[name] = {"fractional_places": PLACES,
                         "rounded_decimal": decimal,
                         "relative_bits_from_arb": bits,
                         "source_manifest_sha256": source_hash,
                         "rounded_decimal_sha256": hashlib.sha256(decimal.encode()).hexdigest()}
        print(f"{name}: exact {PLACES} fractional places PASS; Arb relative bits={bits}; "
              f"digits sha256={outputs[name]['rounded_decimal_sha256']}", flush=True)
    payload = {"quantity": "M11 length and curvature", "source_head_sha": sha,
               "length_panel_sha256": [h for _, h in panels_and_hashes],
               "certificate_scope": "exact endpoints and decimal cell; independently established CI provenance required",
               "results": outputs}
    Path(args.output).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("M11 20000-FRACTIONAL-DECIMAL AUDIT: SUCCESS", flush=True)


if __name__ == "__main__":
    main()
