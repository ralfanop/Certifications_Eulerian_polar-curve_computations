#!/usr/bin/env python3
"""Rigorous Arb 10000-bit ENClosures for M15 Fredholm–Langevin special values.

Only interval values, signs, and enclosures are numerically certified.
The operator Fredholm identity and analytic derivatives are proved in
Lean independently; numerical overlap is NOT a proof of those identities.
No native binary floating-point inputs are used. The required *certified
relative accuracy*, not merely working precision, is >= 8182 bits.
"""
from flint import arb, ctx
import flint

ctx.prec = 10000
assert ctx.prec == 10000
MIN_BITS = 8182
z = arb(0)
o = arb(1)
two = arb(2)
eight = arb(8)
a = o / eight.sqrt()
b = o / two.sqrt()
assert a > z and b > a

def D(x):
    return x.sinh() / x

def Dprime(x):
    return (x * x.cosh() - x.sinh()) / (x * x)

def L(x):
    return x.coth() - o / x

def V(x):
    return o / (x * x) - o / (x.sinh() * x.sinh())

values = {
    "a=1/sqrt(8)": a,
    "b=1/sqrt(2)": b,
    "D(a)=sinh(a)/a": D(a),
    "D(b)=sinh(b)/b": D(b),
    "Dprime(a)": Dprime(a),
    "Dprime(b)": Dprime(b),
    "L(a)": L(a),
    "L(b)": L(b),
    "V(a)": V(a),
    "V(b)": V(b),
    "D(b)-D(a)": D(b) - D(a),
    "L(b)-L(a)": L(b) - L(a),
}
print("Manuscript 15 — true Fredholm/Langevin special scalar values: Arb 10000 working bits")
print("python-flint:", flint.__version__)
print("ctx.prec:", ctx.prec)
for key, value in values.items():
    bits = value.rel_accuracy_bits()
    print(key, "certified relative bits:", bits,
          "ball:", value.str(50, radius=True, more=True))
    assert bits >= MIN_BITS, (key, bits)
    assert value.is_finite(), key

# Strict interval sign tests: both the determinant slope and Langevin
# slope are positive at the special Eulerian points; distinct sampled
# levels satisfy D(b)>D(a), L(b)>L(a).
for key in ["D(a)=sinh(a)/a", "D(b)=sinh(b)/b",
            "Dprime(a)", "Dprime(b)", "L(a)", "L(b)",
            "V(a)", "V(b)", "D(b)-D(a)", "L(b)-L(a)"]:
    assert values[key] > z, key

# Pointwise numeric CONSISTENCY of D'(x)=D(x)*L(x).
# Arb overlap is not an equality proof. The corresponding exact analytic
# identity is a separate Lean proof obligation.
for label, x in [("a", a), ("b", b)]:
    derivative = Dprime(x)
    product = D(x) * L(x)
    assert derivative.overlaps(product), label

# x_E = sqrt(2)*sinh(1/sqrt(2)), as used in M14 section 11:
# x_E and D(b) are compatible independent interval evaluations.
x_E = two.sqrt() * b.sinh()
assert D(b).overlaps(x_E)
print("SUCCESS: twelve rigorous nonzero interval values with at least",
      MIN_BITS, "certified relative bits, strict signs, and overlap checks.")
