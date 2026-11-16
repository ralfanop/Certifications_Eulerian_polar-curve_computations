#!/usr/bin/env python3
"""M14 14.119 §7.4, Theorem 7.5 and Corollary 7.6.
Source ZIP SHA256 ca12498f36da6bfa872f7a36849e64c75fcf483904d772ae3e4c9ad1e81c2c39.
TeX SHA256 b0aba7205b0e915ff49512ffd66f4deeaef29d2de766293be58c090820aeca68.

Enclosures for limiting odd-ladder heat trace and Gibbs quantities at a,b,
using independently expressed exponential/geometric and hyperbolic formulas.
Finite-parameter test of (122)/(124); no actual magnetic eigenvalue computation,
no numerical proof of compactness, asymptotics or the semiclassical limit.
"""
from flint import arb, ctx
from million_decimal_common import record, finish, WORK, MIN

assert WORK == 3600000 and MIN == 3400000 and ctx.prec == WORK

def verify(name, u, v):
    for t in (u, v):
        assert t.is_finite() and not t.contains(0), name
        assert t.rel_accuracy_bits() >= MIN, (name, t.rel_accuracy_bits())
    assert u.overlaps(v), name
    record(name + " (route A)", u)
    record(name + " (route B)", v)

def limiting(x, label):
    q = (-2*x).exp()
    e = (-x).exp()
    z = e/(1-q)
    zh = 1/(2*x.sinh())
    verify(label+" Z", z, zh)
    verify(label+" 2xZ", 2*x*z, x/x.sinh())
    verify(label+" reciprocal 2xZ", 1/(2*x*z), x.sinh()/x)
    mean = (1+q)/(1-q)
    var = 4*q/(1-q)**2
    verify(label+" Gibbs mean", mean, x.cosh()/x.sinh())
    verify(label+" Gibbs variance", var, 1/x.sinh()**2)
    verify(label+" Langevin", mean-1/x, x.cosh()/x.sinh()-1/x)
    verify(label+" Langevin derivative", 1/x**2-var, 1/x**2-1/x.sinh()**2)
    # Exact limiting ladder tail, not a truncation used to infer the PDE limit.
    N = 8
    tail = z*q**N
    exact_tail = (-(2*N+1)*x).exp()/(1-q)
    verify(label+" odd ladder tail N=8", tail, exact_tail)
    half = 1/(2*(x/2).sinh())
    upper = (-(2*N+1)*x/2).exp()*half
    assert tail < upper
    record(label+" half-time tail bound N=8", upper)
    return z

a = 1/arb(8).sqrt()
b = 1/arb(2).sqrt()
verify("b=2a", b, 2*a)
za = limiting(a, "a=1/sqrt(8)")
zb = limiting(b, "b=1/sqrt(2)")
verify("modular reciprocal duplication", b*zb/(a*za), 1/a.cosh())

# Test the explicit oscillator comparison RHS for example parameters only.
# These are not a specific magnetic well, nor measured values of c0/c1.
s, b0, kappa = arb(1), arb(1), arb(2)
h = arb(1)/4
omega = ((1-h)*kappa).sqrt()
upper_h = (s*b0).exp()/(4*(s*omega).sinh()**2)
upper_uniform = (s*b0).exp()/(4*(s*(kappa/2).sqrt()).sinh()**2)
assert upper_h < upper_uniform
record("example oscillator comparison h=1/4", upper_h)
record("example uniform oscillator upper bound", upper_uniform)
finish("m14magnetic")
