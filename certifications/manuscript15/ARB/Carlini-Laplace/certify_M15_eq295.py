#!/usr/bin/env python3
"""FLINT/Arb certificate for Manuscript 15, equations (295)–(296).

Run with python-flint 0.9.0 (FLINT 3.6.0):
    python certify_M15_eq295.py --certificate M15_eq295_balls.json
Newton iterations are only a search for candidate endpoints. The final
strict sign tests, uniqueness, and interval propagation certify the result.
"""
import argparse
import json
import time
from pathlib import Path

import flint
from flint import arb, ctx

P = 3_600_000
MIN_ACCURACY = 3_400_000
PUBLISHED = "112.93167025490469621261195929014436025897847010921393"


def f(u):
    return u * u.tanh() - 1


def newton(u):
    t = u.tanh()
    return (u - (u*t - 1)/(t + u*(1-t*t))).mid()


def dyadic(x):
    m, e = x.man_exp()
    return {"mantissa_hex": hex(int(m)), "exponent_2": int(e)}


def encode_ball(x):
    return {"midpoint": dyadic(x.mid()), "radius": dyadic(x.rad()),
            "rel_accuracy_bits": int(x.rel_accuracy_bits())}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    print(f"python-flint={flint.__version__}; FLINT={flint.__FLINT_VERSION__}", flush=True)
    ctx.prec = 64
    x = arb("1.2").mid()
    for _ in range(6):
        x = newton(x)
    # A 1.5x precision increase leaves ample overlap for quadratic convergence.
    while ctx.prec < P:
        ctx.prec = min(P, ctx.prec * 3 // 2)
        x = newton(x)
        print(f"Newton candidate precision: {ctx.prec}", flush=True)

    # Exact dyadic bracket; no reliance on Newton's numerical error estimate.
    delta = arb((1, -(P-128)))
    a = (x-delta).lower()
    b = (x+delta).upper()
    assert a.is_exact() and b.is_exact() and 0 < a < b
    fa, fb = f(a), f(b)
    assert fa < 0 and fb > 0, "Root bracket not certified"
    # f'(u)=tanh(u)+u sech(u)^2 > 0 for u>0. IVT and strict
    # monotonicity certify that the unique positive root belongs to [a,b].
    u = a.union(b)
    lam = (u*u-1).sqrt()
    assert lam > 0
    # The positive principal arccot is atan(1/lambda).
    alpha = 2*(1/lam).atan()
    degrees = alpha*180/arb.pi()
    # Independent equivalent interval expressions.
    lam_alt = 1/u.sinh()
    alpha_alt = 2*u.sinh().atan()
    assert lam.overlaps(lam_alt) and alpha.overlaps(alpha_alt)
    values = {"u_star": u, "lambda_CL": lam, "alpha_CL_rad": alpha,
              "alpha_CL_deg": degrees}
    for name, value in values.items():
        bits = value.rel_accuracy_bits()
        assert bits >= MIN_ACCURACY, (name, bits)
        print(f"{name}: {value.str(80)}; rel_accuracy_bits={bits}", flush=True)

    # Prove the literal 50-place decimal by rigorous interval comparisons.
    # A printed decimal approximation is not a proof of its own digits.
    scale = 10**50
    n = int(PUBLISHED.replace('.', ''))
    assert len(PUBLISHED.split('.')[1]) == 50
    scaled = degrees * scale
    trunc_ok = scaled >= n and scaled < n+1
    round_ok = scaled > arb(n)-arb(1)/2 and scaled < arb(n)+arb(1)/2
    print(f"Published decimal: {PUBLISHED}", flush=True)
    print(f"50-place truncation matches: {trunc_ok}; rounding matches: {round_ok}", flush=True)
    print(f"f(a)<0 and f(b)>0: PASS; work precision={ctx.prec}", flush=True)
    print(f"Independent formula overlap: PASS; elapsed={time.monotonic()-start:.3f}s", flush=True)
    assert trunc_ok or round_ok
    if args.certificate:
        record = {"equations": [295, 296], "python_flint": flint.__version__,
                  "flint": flint.__FLINT_VERSION__, "working_bits": P,
                  "minimum_relative_bits": MIN_ACCURACY,
                  "root_lower": dyadic(a), "root_upper": dyadic(b),
                  "f_lower": encode_ball(fa), "f_upper": encode_ball(fb),
                  "balls": {k: encode_ball(v) for k,v in values.items()},
                  "published": PUBLISHED, "truncation_matches": bool(trunc_ok),
                  "rounding_matches": bool(round_ok)}
        args.certificate.write_text(json.dumps(record, indent=2)+"\n")
    print("PASS", flush=True)


if __name__ == "__main__":
    main()
