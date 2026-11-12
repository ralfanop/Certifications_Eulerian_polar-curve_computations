#!/usr/bin/env python3
"""Manuscript 15: independent Arb enclosure checks for exact uniform cumulants.

At 10000 working bits, require >=8182 rigorously certified relative bits.
These evaluations concern rational moment combinations, NOT geometric
identities or unproved operator statements. Exact Fraction identities and
Lean kernel proofs (separate workflow job) supply algebraic equality.
No Python floats or approximate decimal inputs are used.
"""
from fractions import Fraction
import flint
from flint import arb, ctx

WORKING_BITS = 10000
MIN_CERTIFIED_BITS = 8182
ctx.prec = WORKING_BITS
assert ctx.prec == WORKING_BITS

q2, q3, q4, q6 = Fraction(1, 12), Fraction(0), Fraction(1, 80), Fraction(1, 448)
qK4 = q4 - 3 * q2**2
qK6 = q6 - 15 * q4 * q2 - 10 * q3**2 + 30 * q2**3
qKurtosis = q4 / q2**2
qExcess = qK4 / q2**2

assert qK4 == Fraction(-1, 120)
assert qK6 == Fraction(1, 252)
assert qKurtosis == Fraction(9, 5)
assert qExcess == Fraction(-6, 5)

a2, a3, a4, a6 = arb(1) / arb(12), arb(0), arb(1) / arb(80), arb(1) / arb(448)
k4 = a4 - arb(3) * a2**2
k6 = a6 - arb(15) * a4 * a2 - arb(10) * a3**2 + arb(30) * a2**3
kurt = a4 / a2**2
excess = k4 / a2**2

assert a2.lower() > 0
assert k4.upper() < 0
assert k6.lower() > 0

results = {
    "actual uniform variance (moment2)": (a2, q2),
    "fourth raw moment": (a4, q4),
    "sixth raw moment": (a6, q6),
    "fourth cumulant": (k4, qK4),
    "sixth cumulant": (k6, qK6),
    "standardized fourth moment": (kurt, qKurtosis),
    "excess kurtosis": (excess, qExcess),
}
print("Manuscript 15 / actual centered uniform cumulant values")
print("python-flint:", flint.__version__)
print("working precision (bits):", ctx.prec)
for name, (ball, exact) in results.items():
    bits = ball.rel_accuracy_bits()
    print(name, ": enclosure", ball.str(90, radius=True, more=True))
    print("  exactly specified target:", exact, "; certified relative bits:", bits)
    assert ball.is_finite(), name
    assert bits >= MIN_CERTIFIED_BITS, (name, bits)
    # Interval overlap is only a numerical consistency check; it does NOT
    # independently prove the exact identity.
    target = arb(exact.numerator) / arb(exact.denominator)
    assert ball.overlaps(target), (name, "ball inconsistent with exact rational")

print("SUCCESS: seven rigorously enclosed nonzero cumulant/moment values at 10000 working bits with >=8182 certified relative bits")
