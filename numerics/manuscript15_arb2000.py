#!/usr/bin/env python3
"""Manuscript 15 — rigorous Arb ball enclosures with >=2300 certified relative bits.

Requires python-flint. No Python floating-point input is used.
This is numerical certification only, not an analytic proof.
"""
import flint
from flint import arb, ctx

WORKING_PRECISION_BITS = 2400
MIN_CERTIFIED_RELATIVE_BITS = 2300
ctx.prec = WORKING_PRECISION_BITS
assert ctx.prec == WORKING_PRECISION_BITS
one = arb(1)
two = arb(2)
four = arb(4)
eight = arb(8)
pi = arb.pi()

values = {
    "r_E(pi) = 2/pi": two / pi,
    "vartheta_E = 2 atan(1/pi)": two * (one / pi).atan(),
    "d_E = 8/pi^3": eight / pi**3,
    "Eulerian area = 2 Si(pi) - 4/pi": two * pi.si() - four / pi,
    "histogram apex = 2 atan(1/2)": two * (one / two).atan(),
    "Plouffe constant = atan(1/2)/pi": (one / two).atan() / pi,
    "r_E(i/sqrt(2))": eight.sqrt() * (one / eight.sqrt()).sinh(),
    "r_E(i sqrt(2))": two.sqrt() * (one / two.sqrt()).sinh(),
    "Langevin at x=1 = coth(1) - 1": one.coth() - one,
}
print("Manuscript 15 — Arb: at least 2300 certified relative bits")
print("python-flint:", flint.__version__)
print("arb working precision:", ctx.prec, "bits")
for name, val in values.items():
    bits = val.rel_accuracy_bits()
    print(name + ":", val.str(720, radius=True, more=True))
    print("  certified relative accuracy:", bits, "bits")
    assert bits >= MIN_CERTIFIED_RELATIVE_BITS, (name, bits, MIN_CERTIFIED_RELATIVE_BITS)

# Ball-overlap checks are consistency checks, not proofs of exact equality.
x0 = one / eight.sqrt()
x1 = one / two.sqrt()
assert values["r_E(i/sqrt(2))"].overlaps(x0.sinh() / x0)
assert values["r_E(i sqrt(2))"].overlaps(x1.sinh() / x1)
assert values["Eulerian area = 2 Si(pi) - 4/pi"].is_finite()
print("SUCCESS — nine rigorously enclosed values, each with >=2300 certified relative bits; no Python float inputs")
