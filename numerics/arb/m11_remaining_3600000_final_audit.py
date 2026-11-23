#!/usr/bin/env python3
"""Fail-closed final numerical audit for the two outstanding M11 quantities.

This program DOES NOT manufacture the missing 3.6M-bit input enclosures.
Its two positional arguments must be the independently generated *complete*
Cauchy-panel and normalized-arclength curvature-continuation manifests.
Both upstream numerical computations and this audit are necessary.

No result at pilot precision can pass, regardless of how many printed
decimal places happen to agree.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

from flint import arb, ctx, fmpz, fmpq
from million_decimal_common import WORK, MIN, DIGITS, exact, record, finish

assert WORK == 3_600_000 and MIN == 3_400_000 and DIGITS == 1_000_001
assert ctx.prec == WORK

def exact_ball(interval, name):
    """Strict enclosure reconstructed from exact rational/dyadic endpoints."""
    lo_raw, hi_raw = (interval[k] for k in ("lower", "upper"))
    lo = fmpq(fmpz(lo_raw["numerator"]), fmpz(lo_raw["denominator"]))
    hi = fmpq(fmpz(hi_raw["numerator"]), fmpz(hi_raw["denominator"]))
    assert lo > 0 and lo <= hi, name
    ball = arb((lo + hi)/2, arb((hi - lo)/2).upper())
    assert ball.lower().fmpq() <= lo and hi <= ball.upper().fmpq(), name
    assert ball.rel_accuracy_bits() >= MIN, (name, ball.rel_accuracy_bits())
    return ball

def assert_rounded(printed, value):
    digits = len(printed.split(".")[1])
    p = Fraction(printed)
    half = Fraction(1, 2*10**digits)
    assert exact(p - half) < value < exact(p + half), printed

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--length-manifest", required=True)
    ap.add_argument("--curvature-manifest", required=True)
    args = ap.parse_args()

    length_bytes = Path(args.length_manifest).read_bytes()
    curvature_bytes = Path(args.curvature_manifest).read_bytes()
    length = json.loads(length_bytes)
    curvature = json.loads(curvature_bytes)

    # The length's *complete* panel combination file is produced by
    # m11_euler_panel.py, not by a single panel.
    assert length["working_bits"] == WORK
    assert length["threshold_bits"] >= MIN
    assert length.get("index") is None, "single panel cannot certify length"
    assert length["panels"] >= 4
    assert "enclosure" in length

    # The curvature file must be the *combined* pair of independent
    # left/right integrals, not a half-panel or a raw Newton iterate.
    par = curvature["parameters"]
    assert par["bits"] == WORK and par["target"] >= MIN
    assert curvature["quantity"] == "D_kappa, Eq. (50)"
    halves = curvature["halves"]
    assert len(halves) == 2
    assert sorted(x["direction"] for x in halves) == [-1, 1]
    assert all("integral" in x and len(x["orders"]) == par["panels"]//2 for x in halves)

    arclength = exact_ball(length["enclosure"], "M11 length, all panels")
    discrepancy = exact_ball(curvature["discrepancy"], "M11 D_kappa, both halves")

    # The length is printed as a PREFIX "5.5510...", not a four-place
    # rounded value. It is deliberately NOT checked as 5.5510 +/- 0.00005.
    assert arb("5.5510") < arclength < arb("5.5511")
    assert_rounded("0.203783759536049443826081", discrepancy)

    print("INPUT exact-head provenance: require CI artifacts from same pinned SHA.", flush=True)
    print("length manifest sha256", sha256(length_bytes).hexdigest(), flush=True)
    print("curvature manifest sha256", sha256(curvature_bytes).hexdigest(), flush=True)
    print("WORK", WORK, "MIN", MIN, "DIGITS", DIGITS, flush=True)
    record("M11 Eq (50) full Eulerian arclength", arclength)
    record("M11 Eq (50) curvature discrepancy D_kappa", discrepancy)
    finish("m11remaining")
    print("M11 BOTH REMAINING 3600000-BIT CERTIFICATES: SUCCESS",flush=True)

if __name__ == "__main__":
    main()
