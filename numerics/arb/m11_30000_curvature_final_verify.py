#!/usr/bin/env python3
"""Fail-closed, independent M11 D_kappa 30,000-fractional-place acceptance gate.

This does not compute the two half-integrals or turn a smoke test into a
certificate. Its input must be actual CI-produced exact-rational manifests,
with a >125k-relative-bit length input for the CURRENT inverse-ODE method.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path
from m11_remaining_3600000_final_audit import (
    endpoint, interval, verify_curvature, same_decimal_cell, exact_decimal,
)
from m11_30000_length_historical_verify import measured_bits

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

PLACES = 30_000
MIN_DK_REL_BITS = 100_100
MIN_LENGTH_REL_BITS = 125_000
MIN_WORK_BITS = 150_000
MIN_PANELS = 128


def load(path):
    data = Path(path).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--combined", required=True)
    p.add_argument("--positive-half", required=True)
    p.add_argument("--negative-half", required=True)
    p.add_argument("--length-manifest", required=True)
    p.add_argument("--length-run-id", required=True, type=int)
    p.add_argument("--length-source-head", required=True)
    p.add_argument("--producer-head", required=True)
    p.add_argument("--output", required=True)
    a = p.parse_args()
    if any(len(s) != 40 or any(c not in "0123456789abcdef" for c in s)
           for s in (a.length_source_head, a.producer_head)):
        raise ValueError("full pinned source and producer SHA-1 required")
    if a.length_run_id <= 0:
        raise ValueError("original length certification run not specified")
    m, combined_sha = load(a.combined)
    length, length_sha = load(a.length_manifest)
    if length.get("index") is not None or int(length.get("panels", 0)) < 32:
        raise ValueError("not a complete rigorously enclosed length manifest")
    length_lo, length_hi = interval(length, "enclosure")
    if not ((length_hi - length_lo) * (1 << MIN_LENGTH_REL_BITS) < length_lo):
        raise ValueError("length interval lacks 125,000 relative bits required by current ODE method")
    params = m.get("parameters", {})
    if int(params.get("bits", 0)) < MIN_WORK_BITS:
        raise ValueError("insufficient FLINT/Arb operating precision")
    if int(params.get("target", 0)) < MIN_DK_REL_BITS:
        raise ValueError("insufficient requested certified curvature bits")
    if int(params.get("panels", 0)) < MIN_PANELS:
        raise ValueError("insufficient independently bounded curvature panels")
    if int(params["panels"]) % 2:
        raise ValueError("curvature panel count must be even")
    halves = {}
    half_hashes = {}
    for direction, path in ((1, a.positive_half), (-1, a.negative_half)):
        one, digest = load(path)
        if one.get("parameters") != params:
            raise ValueError("half source parameters do not match combined result")
        half = one.get("half")
        if not isinstance(half, dict) or half.get("direction") != direction:
            raise ValueError("missing or wrong-direction full curvature half")
        source = half.get("historical_euler_source")
        if not isinstance(source, dict) or (
                source.get("manifest_sha256"), source.get("source_ci"),
                source.get("source_head_sha")) != (
                    length_sha, a.length_run_id, a.length_source_head):
            raise ValueError("curvature chart does not pin the verified high-precision length source")
        halves[direction] = half
        half_hashes[str(direction)] = digest
    if m.get("halves") != [halves[d] for d in (1, -1)] and (
            m.get("halves") != [halves[d] for d in (-1, 1)]):
        raise ValueError("combined curvature halves differ from independent source artifacts")
    lo, hi = verify_curvature(m)
    bits = measured_bits(lo, hi)
    if bits < MIN_DK_REL_BITS:
        raise ValueError(f"measured D_kappa bits {bits} < required {MIN_DK_REL_BITS}")
    decimal = exact_decimal(same_decimal_cell(lo, hi, PLACES), PLACES)
    if len(decimal.split(".")[1]) != PLACES:
        raise ValueError("wrong number of fractional places")
    result = {
        "quantity": "Manuscript 11 D_kappa Eq. (50)",
        "fractional_places": PLACES,
        "rounded_decimal": decimal,
        "decimal_sha256": hashlib.sha256(decimal.encode("ascii")).hexdigest(),
        "measured_arb_relative_bits": bits,
        "combined_sha256": combined_sha,
        "half_manifests_sha256": half_hashes,
        "length_manifest_sha256": length_sha,
        "length_source_run_id": a.length_run_id,
        "length_source_head_sha": a.length_source_head,
        "producer_head_sha": a.producer_head,
        "proof": "full independent half-manifests and high-precision length source pinned; exact square enclosure, printed 24 places, and both rational endpoints strictly in same nearest-even 30,000-place rounding cell",
    }
    Path(a.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("M11 D_KAPPA: 30000 FRACTIONAL DECIMALS STRICT AUDIT SUCCESS")
    print("Measured Arb bits:", bits, "decimal SHA256:", result["decimal_sha256"], flush=True)


if __name__ == "__main__":
    main()
