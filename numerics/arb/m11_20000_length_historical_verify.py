#!/usr/bin/env python3
"""Independently re-audit M11 historical 100k length from ALL original CI artifacts.

The GH workflow must separately prove the historical CI's exact source SHA and
successful completion before invoking this verifier.  No numerical recomputation.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path
from m11_remaining_3600000_final_audit import (
    verify_length, check_bits, same_decimal_cell, exact_decimal, PLACES,
)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def read(path):
    data = Path(path).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--combined", required=True)
    ap.add_argument("--panel-root", required=True)
    ap.add_argument("--source-sha", required=True)
    ap.add_argument("--auditor-sha", required=True)
    ap.add_argument("--source-run", type=int, required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    if args.source_run != 44359739062:
        raise ValueError("unknown historical source CI")
    if args.source_sha != "6ddb354a85832bf5b35538996d7d619c63ac9a16":
        raise ValueError("historical SHA mismatch")
    if len(args.auditor_sha) != 40:
        raise ValueError("auditor HEAD SHA is missing")

    combined, digest = read(args.combined)
    if (combined.get("working_bits"), combined.get("threshold_bits"),
            combined.get("panels"), combined.get("index")) != (110000, 100000, 32, None):
        raise ValueError("not the original 100k full-length combined manifest")
    panel_records, panel_hashes = [], {}
    root = Path(args.panel_root)
    for i in range(32):
        panel_path = root / ("m11-euler-panel-" + str(i)) / "panel.json"
        item, h = read(panel_path)
        panel_records.append(item)
        panel_hashes[str(i)] = h

    lo, hi = verify_length(combined, panel_records)
    bits = check_bits(lo, hi, "historical 32-panel full Eulerian arclength")
    decimal = exact_decimal(same_decimal_cell(lo, hi))
    output = {
        "quantity": "Manuscript 11 full Eulerian arclength L_E",
        "fractional_places": PLACES,
        "rounded_decimal": decimal,
        "decimal_sha256": hashlib.sha256(decimal.encode("ascii")).hexdigest(),
        "source_ci_run_id": args.source_run,
        "historical_source_head_sha": args.source_sha,
        "auditor_head_sha": args.auditor_sha,
        "original_reported_relative_bits": combined["enclosure"]["relative_bits"],
        "audited_arb_reconstruction_relative_bits": bits,
        "combined_manifest_sha256": digest,
        "original_32_panels_sha256": panel_hashes,
        "proof": "all 32 exact panel enclosures summed and enclosed in original combined interval; both endpoints strictly within one exact 20,000-place rounding cell",
    }
    Path(args.output).write_text(json.dumps(output, indent=2) + "\n")
    print("HISTORICAL M11 LENGTH: 20000 FRACTIONAL DECIMALS EXACT AUDIT SUCCESS",
          "panels=32", "Arb bits=", bits, "source SHA=", args.source_sha,
          "decimal SHA256=", output["decimal_sha256"], flush=True)


if __name__ == "__main__":
    main()
