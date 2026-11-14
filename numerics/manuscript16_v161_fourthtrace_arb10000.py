#!/usr/bin/env python3
"""Manuscript 16 v16.1: rigorous FLINT/Arb closed-form trace enclosures.

Analytic spectral identification and classical zeta evaluations are
separate mathematical proof obligations. Here Arb rigorously encloses
the closed expressions at 10000 working bits. No Python float inputs.
"""
import flint
from flint import arb, ctx

WORK_PREC = 10000
MIN_REL_BITS = 8182
ctx.prec = WORK_PREC
assert ctx.prec == WORK_PREC
one = arb(1)
pi = arb.pi()

# Classical exact formulas: zeta(2)=pi²/6, zeta(4)=pi⁴/90,
# zeta(6)=pi⁶/945, zeta(8)=pi⁸/9450.
transverse_trace2 = 2 * (pi**2 / 6 - pi**4 / 90)
dirac_fourth_trace = pi**2 - pi**4 / 12
maxwell_fourth_trace = 2 * (pi**6 / 945 - pi**8 / 9450)
coupled_fourth_trace = dirac_fourth_trace + maxwell_fourth_trace

results = {
    "transverse_trace2": transverse_trace2,
    "dirac_fourth_trace": dirac_fourth_trace,
    "maxwell_fourth_trace": maxwell_fourth_trace,
    "coupled_fourth_trace": coupled_fourth_trace,
}

# Exact integer representations of 12-decimal-place rounding cells.
printed_12 = {
    "transverse_trace2": 1125221666274,
    "dirac_fourth_trace": 1752180148256,
    "maxwell_fourth_trace": 26531411573,
    "coupled_fourth_trace": 1778711559829,
}
print("Manuscript 16 v16.1 — rigorous Arb closed-form trace enclosures")
print("python-flint:", flint.__version__, "Arb working bits:", ctx.prec)
for name, val in results.items():
    assert val.is_finite(), (name, "nonfinite enclosure")
    assert val > 0, (name, "positivity not certified")
    bits = val.rel_accuracy_bits()
    assert bits >= MIN_REL_BITS, (name, bits)
    centre = arb(printed_12[name]) / arb(10**12)
    half_ulp = one / arb(2 * 10**12)
    assert abs(val - centre) < half_ulp, (name, "12-decimal rounding cell")
    print(name, val.str(45, radius=True, more=True),
          "relative_bits", bits, "12dp_numerator", printed_12[name])

print("SUCCESS — v16.1 four trace expressions: Arb 10000-bit enclosures, >=8182 relative bits, certified 12-decimal rounding")
