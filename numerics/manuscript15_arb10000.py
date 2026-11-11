#!/usr/bin/env python3
"""Manuscript 15 — rigorous Arb ball enclosures with >=8182 certified relative bits.

Requires python-flint. No Python floating-point input is used.
This is numerical certification only, not an analytic proof.
"""
import flint
from flint import arb, ctx

WORKING_PRECISION_BITS = 10000
MIN_CERTIFIED_RELATIVE_BITS = 8182
ctx.prec = WORKING_PRECISION_BITS
assert ctx.prec == WORKING_PRECISION_BITS
assert WORKING_PRECISION_BITS > MIN_CERTIFIED_RELATIVE_BITS
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
    "alpha_3 (degrees) = 360 atan(1/2)/pi": two * (one / two).atan() * arb(180) / pi,
    "alpha_3/2 (degrees) = 180 atan(1/2)/pi": (one / two).atan() * arb(180) / pi,
    "vartheta_E (degrees) = 360 atan(1/pi)/pi": two * (one / pi).atan() * arb(180) / pi,
    "r_E(i) = 2 sinh(1/2)": two * (one / two).sinh(),
    "D(1) = sinh(1)": one.sinh(),
}
print("Manuscript 15 — Arb: 10000 working bits and at least 8182 certified relative bits")
print("python-flint:", flint.__version__)
print("arb working precision:", ctx.prec, "bits")
for name, val in values.items():
    bits = val.rel_accuracy_bits()
    print(name + ":", val.str(2670, radius=True, more=True))
    print("  certified relative accuracy:", bits, "bits")
    assert bits >= MIN_CERTIFIED_RELATIVE_BITS, (name, bits, MIN_CERTIFIED_RELATIVE_BITS)

# Figure 1: rigorous 10-decimal-place rounding-cell inclusion.
# Both the centre and the half-unit in the last place are built from
# exact Python integers; the Arb operations give outward enclosures.
alpha_degrees = values["alpha_3 (degrees) = 360 atan(1/2)/pi"]
printed_alpha = arb(531301023542) / arb(10**10)  # 53.1301023542
half_ulp = one / arb(2 * 10**10)
assert abs(alpha_degrees - printed_alpha) < half_ulp, (
    "Figure 1 alpha_3: printed value outside its rounding cell"
)
print("CERTIFIED Figure 1: alpha_3 rounds to 53.1301023542 degrees")

# Ball-overlap checks are consistency checks, not proofs of exact equality.
x0 = one / eight.sqrt()
x1 = one / two.sqrt()
assert values["r_E(i/sqrt(2))"].overlaps(x0.sinh() / x0)
assert values["r_E(i sqrt(2))"].overlaps(x1.sinh() / x1)
assert values["Eulerian area = 2 Si(pi) - 4/pi"].is_finite()
print("SUCCESS — fourteen rigorously enclosed values, each with >=8182 certified relative bits at 10000 working bits; no Python float inputs")
