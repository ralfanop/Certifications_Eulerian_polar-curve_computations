#!/usr/bin/env python3
"""M14 consolidated §7.4: limiting trace and normalized energy moments k=3..8.
Source ZIP SHA256 0614abafe7e9e9a82098278741559bd082028e9d97787f8e0aa4db17e064971d.
TeX SHA256 5eaa4b4c760b8bf347385ecde00033f9a38ba13ed8b60a9b648eaabb69fee662.
Route A: Newton forward differences of (2n+1)^k and geometric binomial sums.
Route B: hyperbolic derivative polynomials, P_0=1,
P_{k+1}(c)=c P_k(c)+(c^2-1)P'_k(c), c=coth(x).
The results are for the limiting odd ladder, not finite-h magnetic eigenvalues.
"""
from flint import arb, ctx
from million_decimal_common import record, finish, WORK, MIN

assert WORK == 3600000 and MIN == 3400000 and ctx.prec == WORK

def verify(label, a, b):
    for t in (a, b):
        assert t.is_finite() and not t.contains(0), label
        assert t.rel_accuracy_bits() >= MIN, (label, t.rel_accuracy_bits())
    assert a.overlaps(b), label
    record(label+" Newton/geometric", a)
    record(label+" hyperbolic/derivative polynomial", b)

def differences(k):
    v = [(2*n+1)**k for n in range(k+1)]
    out = []
    while v:
        out.append(v[0])
        v = [b-a for a,b in zip(v,v[1:])]
    return out

def next_polynomial(p):
    out = [0]*(len(p)+1)
    for j, a in enumerate(p):
        out[j+1] += (j+1)*a
        if j:
            out[j-1] -= j*a
    return out

def eval_polynomial(p, c):
    acc = arb(0)
    for a in reversed(p):
        acc = acc*c+a
    return acc

def moments(x, label):
    q, e = (-2*x).exp(), (-x).exp()
    d = 1-q
    zg = e/d
    zh = 1/(2*x.sinh())
    c = x.cosh()/x.sinh()
    p = [1]
    for k in range(1,9):
        p = next_polynomial(p)
        if k < 3:
            continue
        coeff = differences(k)
        assert all(a > 0 for a in coeff)
        # Newton expansion and sum of binomial coefficients:
        # sum_n C(n,j) q^n = q^j/(1-q)^(j+1).
        raw_a = e*sum((arb(a)*q**j/d**(j+1) for j,a in enumerate(coeff)), arb(0))
        normalized_b = eval_polynomial(p,c)
        raw_b = zh*normalized_b
        normalized_a = raw_a/zg
        assert raw_a > 0 and raw_b > 0
        # signed derivative d^k Z/dx^k
        verify(f"{label} signed heat derivative k={k}",
               (-1)**k*raw_a, (-1)**k*raw_b)
        verify(f"{label} normalized raw Gibbs moment k={k}",
               normalized_a, normalized_b)

moments(1/arb(8).sqrt(), "a=1/sqrt(8)")
moments(1/arb(2).sqrt(), "b=1/sqrt(2)")
finish("m14highermoments")
