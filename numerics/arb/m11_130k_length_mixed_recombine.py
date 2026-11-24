#!/usr/bin/env python3
"""Recombine original M11 length panels from two different VERIFIED CIs.

Uses the successful 13 panels of the original 150k pilot and 19 NEW
130k panels; compares each higher-precision rational interval with the
historical 100k panel interval. Does not perform any integration itself.
"""
import argparse, hashlib, json, sys
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx, fmpq, fmpz
from m11_remaining_3600000_final_audit import interval, same_decimal_cell, exact_decimal
from m11_euler_cauchy import exact_endpoints

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

OLD = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17}
NEW = set(range(32)) - OLD
PILOT_RUN, PILOT_HEAD = 45157228615, "688c66a8284bd801809bb1d3e21e03eafb86aeee"
HIST_RUN, HIST_HEAD = 44359739062, "6ddb354a85832bf5b35538996d7d619c63ac9a16"
MIN_REL_BITS, WORK_BITS = 130_000, 155_000


def read(path):
    raw = Path(path).read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def check_panel(obj, idx, expected_bits, expected_target):
    if tuple(obj.get(x) for x in ("index", "panels", "working_bits", "threshold_bits")) != (
            idx, 32, expected_bits, expected_target):
        raise ValueError(f"panel {idx}: wrong source precision or interval")
    return interval(obj, "enclosure")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original-150k-root", required=True)
    p.add_argument("--new-130k-root", required=True)
    p.add_argument("--historical-100k-root", required=True)
    p.add_argument("--source-run", type=int, required=True)
    p.add_argument("--original-run", type=int, required=True)
    p.add_argument("--auditor-head", required=True)
    p.add_argument("--output", required=True)
    a = p.parse_args()
    if (a.source_run, a.original_run) != (HIST_RUN, PILOT_RUN):
        raise ValueError("historical source IDs changed")
    if len(a.auditor_head) != 40:
        raise ValueError("auditor source HEAD missing")
    historic_combined, historic_sha = read(
        Path(a.historical_100k_root) / "m11-euler-panel-certified-100k" / "m11-euler-panel-100k.json")
    if historic_sha != "a606d305f7d4c773695cee61cf56268022ec9cc5525f689f301e8822f22fe7b5":
        raise ValueError("original complete length manifest SHA mismatch")
    original, oldfiles = Path(a.original_150k_root), []
    fresh, newfiles = Path(a.new_130k_root), []
    for i in OLD:
        oldfiles.append(original / f"m11-length-150k-panel-{i}" / "panel.json")
    for i in NEW:
        newfiles.append(fresh / f"m11-length-130k-new-panel-{i}" / "panel.json")
    if any(not path.is_file() for path in oldfiles + newfiles):
        raise ValueError("not all 32 high precision panels are available")
    total_lo, total_hi = Fraction(0), Fraction(0)
    sources = {}
    for i in range(32):
        historic, _ = read(Path(a.historical_100k_root) / f"m11-euler-panel-{i}" / "panel.json")
        h_lo, h_hi = check_panel(historic, i, 110000, 100000)
        sourcepath = (original / f"m11-length-150k-panel-{i}" / "panel.json" if i in OLD else
                      fresh / f"m11-length-130k-new-panel-{i}" / "panel.json")
        manifest, digest = read(sourcepath)
        s_lo, s_hi = check_panel(manifest, i, *( (170000, 150000) if i in OLD else (155000, 130000)))
        if not (h_lo <= s_lo <= s_hi <= h_hi):
            raise ValueError(f"high precision panel {i} lies outside original verified panel interval")
        total_lo += s_lo
        total_hi += s_hi
        sources[str(i)] = {
            "run_id": PILOT_RUN if i in OLD else None,
            "source_head_sha": PILOT_HEAD if i in OLD else a.auditor_head,
            "source_manifest_sha256": digest,
            "working_bits": manifest["working_bits"],
            "threshold_bits": manifest["threshold_bits"],
        }
    original_lo, original_hi = interval(historic_combined, "enclosure")
    if not (original_lo <= total_lo <= total_hi <= original_hi):
        raise ValueError("recombined new high-precision length lies outside original certified full length")
    ctx.prec = WORK_BITS
    lo_q = fmpq(fmpz(total_lo.numerator), fmpz(total_lo.denominator))
    hi_q = fmpq(fmpz(total_hi.numerator), fmpz(total_hi.denominator))
    ball = arb((lo_q + hi_q) / 2, arb((hi_q - lo_q) / 2).upper())
    if not (ball.lower().fmpq() <= lo_q <= hi_q <= ball.upper().fmpq()):
        raise ValueError("Arb does not enclose the exact 32-panel sum")
    bits = ball.rel_accuracy_bits()
    if bits < MIN_REL_BITS:
        raise ValueError(f"complete length only {bits} relative bits; need {MIN_REL_BITS}")
    if not (arb("5.5510") < ball < arb("5.5511")):
        raise ValueError("published full length prefix mismatch")
    rounded = exact_decimal(same_decimal_cell(total_lo, total_hi, 30000), 30000)
    manifest = {
        "quantity": "M11 full Eulerian length input for 30k-decimal D_kappa ODE",
        "working_bits": WORK_BITS,
        "threshold_bits": MIN_REL_BITS,
        "panels": 32,
        "index": None,
        "enclosure": exact_endpoints(ball),
        "original_100k_source_run": HIST_RUN,
        "original_100k_source_head_sha": HIST_HEAD,
        "original_100k_combined_sha256": historic_sha,
        "original_150k_partial_source_run": PILOT_RUN,
        "original_150k_partial_source_head_sha": PILOT_HEAD,
        "original_150k_reused_panel_indices": sorted(OLD),
        "new_130k_panel_indices": sorted(NEW),
        "panel_sources": sources,
        "source_head_sha": a.auditor_head,
        "original_30000_decimal_sha256": hashlib.sha256(rounded.encode("ascii")).hexdigest(),
    }
    Path(a.output).write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("M11 L_E 130K CURVATURE-CHART INPUT EXACT RECOMBINATION SUCCESS")
    print("all 32 panels verified; 13 previous 150k reused; 19 new 130k")
    print("measured relative bits:", bits, "original length source:", HIST_RUN, flush=True)


if __name__ == "__main__":
    main()
