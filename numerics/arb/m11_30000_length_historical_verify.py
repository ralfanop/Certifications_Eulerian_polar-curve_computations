#!/usr/bin/env python3
"""Exact independent re-audit of the ORIGINAL M11 length at 30,000 fractional places.

No quadrature or Taylor series is recomputed.  The caller MUST download all
33 archived artifacts from GitHub Actions run 44359739062 after independently
checking its success and original source SHA.  Any missing panel fails closed.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

from flint import arb, ctx, fmpq, fmpz
from m11_remaining_3600000_final_audit import (
    verify_length, same_decimal_cell, exact_decimal,
)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

PLACES = 30_000
MIN_REL_BITS = 99_800
ARB_WORK_BITS = 110_000
ORIGINAL_RUN = 44359739062
ORIGINAL_HEAD = "6ddb354a85832bf5b35538996d7d619c63ac9a16"
ORIGINAL_COMBINED_SHA256 = (
    "a606d305f7d4c773695cee61cf56268022ec9cc5525f689f301e8822f22fe7b5"
)


def read(path):
    raw = Path(path).read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def measured_bits(lo, hi):
    """Independently reconstruct an Arb ball containing BOTH exact endpoints."""
    if not 0 < lo <= hi:
        raise ValueError("length interval is not strictly positive")
    ctx.prec = ARB_WORK_BITS
    a = fmpq(fmpz(lo.numerator), fmpz(lo.denominator))
    b = fmpq(fmpz(hi.numerator), fmpz(hi.denominator))
    ball = arb((a + b) / 2, arb((b - a) / 2).upper())
    if not (ball.lower().fmpq() <= a and b <= ball.upper().fmpq()):
        raise ValueError("Arb reconstruction does not enclose exact endpoints")
    bits = int(ball.rel_accuracy_bits())
    if bits < MIN_REL_BITS:
        raise ValueError(f"Only {bits} measured relative bits; need {MIN_REL_BITS}")
    return bits


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--combined", required=True)
    p.add_argument("--panel-root", required=True)
    p.add_argument("--source-run", type=int, required=True)
    p.add_argument("--source-sha", required=True)
    p.add_argument("--auditor-sha", required=True)
    p.add_argument("--output", required=True)
    args = p.parse_args()
    if (args.source_run, args.source_sha) != (ORIGINAL_RUN, ORIGINAL_HEAD):
        raise ValueError("incorrect historical provenance")
    if (len(args.auditor_sha) != 40 or
            any(c not in "0123456789abcdef" for c in args.auditor_sha)):
        raise ValueError("exact full lowercase auditor HEAD SHA required")
    combined, combined_sha = read(args.combined)
    if combined_sha != ORIGINAL_COMBINED_SHA256:
        raise ValueError("historical combined manifest SHA256 mismatch")
    if tuple(combined.get(k) for k in
             ("working_bits", "threshold_bits", "panels", "index")) != (
             110000, 100000, 32, None):
        raise ValueError("historical 100k length parameters mismatch")
    root = Path(args.panel_root)
    records, panel_hashes = [], {}
    for i in range(32):
        record, digest = read(root / f"m11-euler-panel-{i}" / "panel.json")
        records.append(record)
        panel_hashes[str(i)] = digest
    lo, hi = verify_length(combined, records)
    bits = measured_bits(lo, hi)
    rounded = exact_decimal(same_decimal_cell(lo, hi, PLACES), PLACES)
    if len(rounded.split(".")[1]) != PLACES:
        raise ValueError("not exactly 30,000 fractional places")
    result = {
        "quantity": "M11 full Eulerian arclength L_E, Eq. (50)",
        "fractional_places": PLACES,
        "rounded_decimal": rounded,
        "decimal_sha256": hashlib.sha256(rounded.encode("ascii")).hexdigest(),
        "measured_arb_relative_bits": bits,
        "minimum_required_relative_bits": MIN_REL_BITS,
        "original_run_id": ORIGINAL_RUN,
        "original_head_sha": ORIGINAL_HEAD,
        "auditor_head_sha": args.auditor_sha,
        "original_combined_manifest_sha256": combined_sha,
        "original_32_panel_sha256": panel_hashes,
        "original_reported_relative_bits": combined["enclosure"]["relative_bits"],
        "proof": "original 32 exact intervals recombined, original combined enclosure checked, both endpoints strictly inside identical 30,000-place nearest-even rounding cell",
    }
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("M11 L_E: 30000 FRACTIONAL DECIMALS STRICT EXACT AUDIT SUCCESS")
    print("Arb relative bits:", bits, "source run:", ORIGINAL_RUN,
          "digit SHA256:", result["decimal_sha256"], flush=True)


if __name__ == "__main__":
    main()
