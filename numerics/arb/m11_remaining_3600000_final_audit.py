#!/usr/bin/env python3
"""M11 exact 20,000-fractional-decimal acceptance gate; fail closed.

Accepts only complete, independently produced, rigorously bounded manifests.
This auditor does not manufacture enclosures or certify their provenance by itself.
"""
import argparse
import hashlib
import json
from decimal import Decimal, localcontext, ROUND_HALF_EVEN
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx, fmpq, fmpz

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
    x = manifest[key]
    lo, hi = endpoint(x["lower"]), endpoint(x["upper"])
    if not 0 < lo <= hi:
        raise ValueError("invalid positive enclosure")
    return lo, hi

def same_decimal_cell(lo, hi, places=PLACES):
    """Exact half-unit-in-last-place inequalities; no floating point."""
    scale = 10 ** places
    def nearest_even(x):
        num, den = x.numerator * scale, x.denominator
        q, r = divmod(num, den)
        return q + int(2*r > den or (2*r == den and q % 2 == 1))
    k = nearest_even(lo)
    if nearest_even(hi) != k:
        raise ValueError("endpoint decimal cells disagree")
    lower, upper = Fraction(2*k-1, 2*scale), Fraction(2*k+1, 2*scale)
    if not (lower < lo <= hi < upper):
        raise ValueError("enclosure touches decimal rounding boundary")
    return k

def check_bits(lo, hi, name):
    ctx.prec = WORK_BITS
    l, h = fmpq(fmpz(lo.numerator), fmpz(lo.denominator)), fmpq(fmpz(hi.numerator), fmpz(hi.denominator))
    ball = arb((l+h)/2, arb((h-l)/2).upper())
    if not (ball.lower().fmpq() <= l and h <= ball.upper().fmpq()):
        raise ValueError(name + ": Arb failed to enclose exact endpoints")
    bits = ball.rel_accuracy_bits()
    if bits < MIN_REL_BITS:
        raise ValueError(f"{name}: {bits} relative bits < {MIN_REL_BITS}")
    return bits

def verify_length(m):
    if m.get("index") is not None or int(m.get("panels", 0)) < 32:
        raise ValueError("length must be combined from >=32 panels")
    lo, hi = interval(m, "enclosure")
    if not (Fraction("5.5510") < lo <= hi < Fraction("5.5511")):
        raise ValueError("published length prefix inconsistent")
    return lo, hi

def verify_curvature(m):
    if m.get("quantity") != "D_kappa, Eq. (50)":
        raise ValueError("wrong curvature quantity")
    halves = m.get("halves", [])
    if len(halves) != 2 or sorted(h.get("direction") for h in halves) != [-1, 1]:
        raise ValueError("both independently integrated halves required")
    if any("integral" not in h or not h.get("orders") for h in halves):
        raise ValueError("incomplete curvature halves")
    lo, hi = interval(m, "discrepancy")
    scale = 10 ** 24
    printed = Fraction(PRINTED_DK)
    if not (printed-Fraction(1,2*scale) < lo <= hi < printed+Fraction(1,2*scale)):
        raise ValueError("published 24-decimal curvature cell mismatch")
    return lo, hi

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--length-manifest", required=True)
    p.add_argument("--curvature-manifest", required=True)
    p.add_argument("--expected-head-sha", required=True)
    args = p.parse_args()
    if len(args.expected_head_sha) != 40 or any(c not in "0123456789abcdef" for c in args.expected_head_sha):
        raise ValueError("full lowercase HEAD SHA required")
    for name, path, validator in (("length", args.length_manifest, verify_length),
                                  ("curvature", args.curvature_manifest, verify_curvature)):
        data = Path(path).read_bytes()
        m = json.loads(data)
        if m.get("head_sha") != args.expected_head_sha:
            raise ValueError(name + ": manifest HEAD SHA mismatch or missing")
        lo, hi = validator(m)
        bits = check_bits(lo, hi, name)
        cell = same_decimal_cell(lo, hi)
        print(f"{name}: exact 20000 fractional digits verified; relative bits={bits}; cell integer={cell}", flush=True)
        print(f"{name}: manifest sha256={hashlib.sha256(data).hexdigest()}", flush=True)
    print("M11 20000 FRACTIONAL DECIMAL CELL AUDIT: SUCCESS (input provenance requires independent CI verification)", flush=True)

if __name__ == "__main__":
    main()
