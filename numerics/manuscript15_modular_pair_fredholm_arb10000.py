#!/usr/bin/env python3
"""Rigorous 10000-bit Arb intervals at the modularly paired imaginary points.

z0 = i / sqrt(2), z1 = i * sqrt(2) = -1/z0.  Their classical modular
j invariant agrees, but that fact alone does NOT imply the associated
Fredholm determinant or Langevin values are equal.

For the independently established Dirichlet-inverse spectral model,
D(x) = det_F(I + x^2 T_D) = sinh(x)/x.  At x=i*t with t>0,
D(i*t)=sin(t)/t, while Im L(i*t)=1/t-cot(t).
All evaluations below are outward interval enclosures using
python-flint Arb at precisely 10000 working bits.  Interval overlap
tests are checks, not analytic proofs or a new modular theorem.
The operator identity remains a separate Lean obligation.
"""
from flint import arb, ctx
import flint

ctx.prec = 10000
assert ctx.prec == 10000
MIN_CERTIFIED_BITS = 8182
zero, one, two = arb(0), arb(1), arb(2)
a = one / two.sqrt()   # Im(z0)
b = two.sqrt()         # Im(z1)
assert zero < a < b

def dirichlet_fredholm_on_imag(t):
    return t.sin() / t

def langevin_imaginary_coefficient(t):
    return one / t - t.cos() / t.sin()

def fredholm_complex_derivative_imaginary_coefficient(t):
    # D'(i*t) = i * (sin(t)-t*cos(t))/t^2.
    return (t.sin() - t * t.cos()) / (t * t)

Da = dirichlet_fredholm_on_imag(a)
Db = dirichlet_fredholm_on_imag(b)
La = langevin_imaginary_coefficient(a)
Lb = langevin_imaginary_coefficient(b)
Dpa = fredholm_complex_derivative_imaginary_coefficient(a)
Dpb = fredholm_complex_derivative_imaginary_coefficient(b)

values = {
    "Im(z0)=1/sqrt(2)": a,
    "Im(z1)=sqrt(2)": b,
    "D(z0)=sin(a)/a": Da,
    "D(z1)=sin(b)/b": Db,
    "D(z0)-D(z1)": Da - Db,
    "Im L(z0)": La,
    "Im L(z1)": Lb,
    "Im L(z1)-Im L(z0)": Lb - La,
    "Im Dprime(z0)": Dpa,
    "Im Dprime(z1)": Dpb,
}
print("Manuscript 15 — imaginary modular-pair spectral values; Arb 10000 bits")
print("python-flint", flint.__version__)
print("working precision", ctx.prec)
for name, val in values.items():
    bits = val.rel_accuracy_bits()
    print(name, "certified bits:", bits, "ball:", val.str(50, radius=True, more=True))
    assert val.is_finite(), name
    assert bits >= MIN_CERTIFIED_BITS, (name, bits)
    assert val > zero, (name, val)

# D(z0) is strictly larger than D(z1) although j(z0)=j(z1)=8000.
# The modular j-identity is a classical exact result NOT certified here;
# this script certifies only the stated special scalar inequalities.
assert Da > Db
assert Lb > La

# Consistency with D'(x) = D(x) L(x) at x=i*a and x=i*b:
# these overlaps DO NOT constitute an analytic equality proof.
assert Dpa.overlaps(Da * La)
assert Dpb.overlaps(Db * Lb)

# Equivalent spectral parameters for the operator determinant are
# z0^2=-1/2 and z1^2=-2; check their exact real-ball arithmetic.
assert (-(a * a)).overlaps(-one / two)
assert (-(b * b)).overlaps(-two)

print("SUCCESS: ten strictly positive 10000-bit Arb enclosures with >=",
      MIN_CERTIFIED_BITS, "certified relative bits; strict D and L separation.")
