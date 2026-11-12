#!/usr/bin/env python3
"""M11--15: independent Arb tests of Eulerian duplication and spectral trace identities.

All values here are interval enclosures, NOT formal proofs of the
infinite-dimensional Fredholm identities or of operator unitary equivalence.
The identities invoked are precisely the classical Eulerian/Dirichlet spectral
formulas stated in Manuscripts 12, 14 and 15.

The real parameter is a=1/sqrt(8); the modular points are z0=2 i a
and z1=4 i a.  IMPORTANT: r_E(z0)=sinh(a)/a, NOT D(z0)=sin(Im(z0))/Im(z0).
Truncation errors are bounded by elementary integral-test bounds rather
than claimed to have 8182-bit relative accuracy.
"""
from flint import arb, ctx
import flint

WORK_BITS = 10000
MIN_BITS = 8182
ctx.prec = WORK_BITS
assert ctx.prec == WORK_BITS

O, T, F = arb(1), arb(2), arb(4)
Z = arb(0)
a = O / arb(8).sqrt()
b = T * a
pi2 = arb.pi() ** 2

def D1(x):  # genuine Dirichlet inverse Fredholm determinant, via known scalar formula
    return x.sinh() / x

def D2(x):  # length-two Dirichlet spectral product
    return (T*x).sinh() / (T*x)

def Ddn(x):  # Dirichlet-Neumann spectral product
    return x.cosh()

def L(x):
    return x.cosh() / x.sinh() - O / x

def V(x):
    return O/(x*x) - O/(x.sinh() * x.sinh())

r0, r1 = D1(a), D2(a)
q = r0 / r1
q_independent = O / Ddn(a)
tanh_a = a.sinh() / a.cosh()
L_a, L_2a = L(a), L(b)
V_a, V_2a = V(a), V(b)
td_a = L_a/(T*a)
tdn_a = tanh_a/(T*a)
td2_a = L_2a/a
D1_deriv = (a * a.cosh() - a.sinh())/(a*a)
D2_deriv = ((T*a)*(T*a).cosh() - (T*a).sinh())/(T*a*a)
q_deriv = (D1_deriv*r1 - r0*D2_deriv)/(r1*r1)
minus_log_q_deriv = -q_deriv/q

positive_values = {
    "a = 1/sqrt(8)": a,
    "b = 2a = 1/sqrt(2)": b,
    "rE(z0) = sinh(a)/a": r0,
    "rE(z1) = sinh(2a)/(2a)": r1,
    "rE(z1)-rE(z0)": r1-r0,
    "qE(a) = rE(z0)/rE(z1)": q,
    "cosh(a)": a.cosh(),
    "sech(a)": q_independent,
    "tanh(a)": tanh_a,
    "L(a)": L_a,
    "L(2a)": L_2a,
    "Lprime(a)": V_a,
    "Lprime(2a)": V_2a,
    "DN Fredholm determinant = cosh(a)": Ddn(a),
    "Dirichlet trace, spectral formula": td_a,
    "DN trace, spectral formula": tdn_a,
    "length-2 Dirichlet trace, spectral formula": td2_a,
    "-(d/dt)log(qE(t)) at a, quotient differentiation": minus_log_q_deriv,
}
print("M11-15 Eulerian duplication/Fredholm/Langevin Arb certificates")
print("python-flint", flint.__version__, "working precision", ctx.prec)
min_bits = WORK_BITS
for name, val in positive_values.items():
    bits = val.rel_accuracy_bits()
    min_bits = min(min_bits, bits)
    assert val.is_finite(), name
    assert bits >= MIN_BITS, (name, bits)
    assert val > Z, (name, val)
    print(name, "certified relative bits:", bits,
          "ball:", val.str(45, radius=True, more=True))

def overlap(name, x, y):
    assert x.overlaps(y), (name, x, y)
    print("CONSISTENCY (overlap only, NOT proof of exact identity):", name)

# Independent interval evaluations of the manuscript's exact analytic identities.
overlap("rE(z1) = cosh(a)*rE(z0)", r1, r0 * Ddn(a))
overlap("qE(a) = sech(a)", q, q_independent)
overlap("D2(a)=D1(a)*DDN(a)", D2(a), D1(a)*Ddn(a))
overlap("2L(2a)=L(a)+tanh(a)", T*L_2a, L_a+tanh_a)
overlap("-d log(qE)/dt = tanh(a)", minus_log_q_deriv, tanh_a)
overlap("T_D + T_DN = T_D2", td_a+tdn_a, td2_a)
overlap("L(a)=2a T_D(a)", L_a, T*a*td_a)
overlap("tanh(a)=2a T_DN(a)", tanh_a, T*a*tdn_a)
overlap("2L(2a)=2a T_D2(a)", T*L_2a, T*a*td2_a)
assert r1 > r0
assert L_2a > L_a

# Independent finite-rank spectral sums and mathematically valid
# tail bounds (integral test), NOT 8182-bit tail accuracies.
# Eigenvalues for A1, ADN, A2 respectively:
# pi^2 (n+1)^2, pi^2 (n+1/2)^2, pi^2 (n+1)^2/4.
# For x>=0, bound denominators below by eigenvalues and use
# sum_{n>=N} 1/(n+1)^2 <= 1/N and
# sum_{n>=N} 1/(n+1/2)^2 <= 1/(N-1/2), N>=1.
for n in (8, 32, 128):
    fd = Z
    fn = Z
    f2 = Z
    for k in range(n):
        k1 = arb(k+1)
        kh = arb(k) + O/T
        fd += O/(pi2*k1*k1 + a*a)
        fn += O/(pi2*kh*kh + a*a)
        f2 += O/(pi2*k1*k1/F + a*a)
    tail_d = td_a - fd
    tail_dn = tdn_a - fn
    tail_2 = td2_a - f2
    bd = O / (pi2 * arb(n))
    bdn = O / (pi2 * (arb(n) - O/T))
    b2 = F / (pi2 * arb(n))
    assert Z < tail_d < bd, ("A1 tail bound", n)
    assert Z < tail_dn < bdn, ("ADN tail bound", n)
    assert Z < tail_2 < b2, ("A2 tail bound", n)
    print("TAIL", n, "A1", tail_d.str(25, radius=True, more=True),
          "<", bd.str(25, radius=True, more=True))
    print("TAIL", n, "DN", tail_dn.str(25, radius=True, more=True),
          "<", bdn.str(25, radius=True, more=True))
    print("TAIL", n, "A2", tail_2.str(25, radius=True, more=True),
          "<", b2.str(25, radius=True, more=True))

print("SUCCESS: Eulerian duplication, Langevin identities, and three")
print("genuine spectral truncation tail families; minimum certified")
print("relative scalar bits:", min_bits, "(required:", MIN_BITS, ")")
