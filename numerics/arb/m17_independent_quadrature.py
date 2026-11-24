#!/usr/bin/env python3
"""Independent FLINT/Arb cross-check of the M17 Cassini constants.

M17 (Cyclohedral.tex, 24 Nov 2026), Theorem thm:m17-curvature-area,
Eqs. m17-area, m17-area-integration, m17-L8-integral.

Unlike the closed-form certificate (numerics/arb/m17_cassini_area_30000_decimal.py),
which evaluates log(1+sqrt2)/sqrt2 and an algebraically equivalent log form,
this script evaluates the two *integrals* written in the manuscript by
rigorous Arb quadrature (acb.integral, Petras algorithm with certified
error bounds) and checks that every ball overlaps the closed-form ball:

  I_L = int_0^1 (1 - x^2)/(1 + x^4) dx                 (= L8(1,chi2))
  I_A = 2*pi * int_0^1 nu^2/(2 - nu^2)^2 dnu           (= lobe area)
  T   = atanh(1/sqrt2)/sqrt2 via Arb's atanh           (third route to L8)

Numerical agreement does not replace the proofs in the manuscript.
"""
import hashlib
import json
import sys

import flint
from flint import acb, arb, ctx

assert flint.__version__ == "0.9.0"
BITS = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
ctx.prec = BITS


def overlap(a, b):
    return not (a < b or a > b)


def main():
    sqrt2 = arb(2).sqrt()
    pi = arb.pi()
    l8_closed = (1 + sqrt2).log() / sqrt2
    area_closed = pi * (1 - l8_closed)

    f_l = lambda x, _: (1 - x * x) / (1 + x ** 4)
    f_a = lambda x, _: x * x / (2 - x * x) ** 2
    i_l = acb.integral(f_l, 0, 1).real
    i_a = 2 * pi * acb.integral(f_a, 0, 1).real
    l8_atanh = (1 / sqrt2).atanh() / sqrt2

    checks = {
        "L8 quadrature vs closed form": overlap(i_l, l8_closed),
        "L8 atanh vs closed form": overlap(l8_atanh, l8_closed),
        "area quadrature vs closed form": overlap(i_a, area_closed),
    }
    acc = {
        "L8 quadrature": i_l.rel_accuracy_bits(),
        "L8 atanh": l8_atanh.rel_accuracy_bits(),
        "area quadrature": i_a.rel_accuracy_bits(),
    }
    out = {
        "backend": "FLINT/Arb via python-flint " + flint.__version__,
        "working_bits": BITS,
        "relative_accuracy_bits": acc,
        "overlap_checks": checks,
        "L8_quadrature_ball_head": i_l.str(60, radius=True),
        "area_quadrature_ball_head": i_a.str(60, radius=True),
    }
    print(json.dumps(out, indent=2))
    assert all(checks.values()), checks
    print("SUCCESS independent quadrature cross-check at", BITS, "bits")


if __name__ == "__main__":
    main()
