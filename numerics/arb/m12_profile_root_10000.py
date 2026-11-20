#!/usr/bin/env python3
"""M12: 10000-bit actual profile root checkpoint using the periodic-strip and interval
Newton methods from #418 and #390. No million-digit claim."""
import argparse
import json
import resource
import time
from pathlib import Path
from fractions import Fraction as Q
from flint import arb, acb, ctx
from million_decimal_common import exact
from m12_profile_interval_newton import A, ROWS, initial, integrals, printed_check
from m12_profile_periodic_strip import periodic

def solve(row, P):
    start = time.monotonic()
    X = initial(row, 256)  # strict signs; unique positive root
    target = Q(row)
    for i in range(32):
        b = X.rel_accuracy_bits()
        # Enclose the derivative uniformly on the complete current root ball.
        ctx.prec = max(128, b + 96)
        t = time.monotonic()
        D = integrals(X, True, goal=max(40, b-48))
        dt = time.monotonic()-t
        assert D.is_finite() and D > 0
        assert D.rel_accuracy_bits() >= b-100
        # Use the periodic strip with a verified analytic tail for the
        # point residual; the midpoint is an exact dyadic number.
        ctx.prec = min(P, max(384, 2*b+96))
        m = X.mid()
        t = time.monotonic()
        H = periodic(m, ctx.prec-48)
        ht = time.monotonic()-t
        Y = m-(H-exact(target))/D
        assert Y.is_finite() and Y > 0
        Z = X.intersection(Y)
        assert Z.rel_accuracy_bits() > b
        X = Z
        F = A(acb(X)).real**2/4
        bits = F.rel_accuracy_bits()
        print("ROOT STEP", row, "p", ctx.prec, "root bits",
              X.rel_accuracy_bits(), "F bits", bits,
              "derivative seconds", dt, "periodic seconds", ht, flush=True)
        if bits >= P-120:
            ctx.prec = P
            F = A(acb(X)).real**2/4
            printed_check(row, F)
            assert F.rel_accuracy_bits() >= P-120
            # Explicit independent lower-precision comparison, not a
            # requirement to duplicate the expensive high-precision run.
            ctx.prec = 256
            reference = initial(row, 256)
            assert reference.overlaps(X)
            ctx.prec = P
            data = {
                "row": row, "working_bits": P,
                "relative_bits": F.rel_accuracy_bits(),
                "root_lower": str(X.lower().fmpq()),
                "root_upper": str(X.upper().fmpq()),
                "F_lower": str(F.lower().fmpq()),
                "F_upper": str(F.upper().fmpq()),
                "elapsed_seconds": time.monotonic()-start,
                "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            }
            Path("profile-root-pilot.json").write_text(json.dumps(data)+"\n")
            print("PROFILE ROOT PILOT PASS", row, P, data["relative_bits"],
                  "seconds", data["elapsed_seconds"],
                  "peak RSS KiB", data["peak_rss_kib"], flush=True)
            return
    raise RuntimeError("root contraction did not reach target")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("row", choices=ROWS)
    ap.add_argument("--bits", type=int, choices=[10000], required=True)
    ns = ap.parse_args()
    solve(ns.row, ns.bits)
