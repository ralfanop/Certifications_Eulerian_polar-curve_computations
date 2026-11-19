#!/usr/bin/env python3
"""M12 independent streaming periodic-strip quadrature pilot.

A(s)=coth(s/2)/2-1/s is odd.  Put B(S,s)=(A(S)-A(s))/(S-s)
with the removable value at s=S.  Then
 A(S)^2-A(s)^2=(S^2-s^2) B(S,s) B(S,-s).
With s=S sin(theta),
 H(S)= S^2/pi integral_0^{pi/2} f(theta) dtheta,
 f=cos(theta)^2 sqrt(B(S,s) B(S,-s)).
f is even and pi-periodic. The mean over 2pi is 2/pi times
the quadrant integral, so H=S^2/2 times the periodic mean.
On a certified strip |Im theta|<=a with |f|<=M, shifting the
Fourier contour gives |c_k|<=M exp(-a |k|). Aliasing yields
 |H - (S^2/(2N)) sum_{k=0}^{N-1} f(2pi*k/N)|
 <= S^2 M/(exp(a*N)-1).
All strip bounds and summands are rigorous Arb balls. No Fourier
sampling assumption or heuristic stopping criterion is used.
The summation is streaming, constant number of live balls; unlike a
length-O(precision) Taylor series, no large coefficient array is stored.
This is a scaling pilot, not a million-decimal certificate.
"""
import argparse
import time
from flint import arb, acb, ctx
from m12_profile_interval_newton import A, exprel, integrals
from million_decimal_common import exact

def B(S,s):
    a=A(S)
    delta=S-s
    # Direct quotient away from the endpoint; stable removable quotient
    # near the endpoint. Both formulas are mathematically identical.
    if abs(delta).lower() > abs(S).upper()/8:
        return (a-A(s))/delta
    return 1/(S*s)-s.exp()*exprel(delta)/(S.expm1()*s.expm1())

def f(S,theta):
    s=S*theta.sin()
    c=theta.cos()
    return c*c*(B(S,s)*B(S,-s)).sqrt(analytic=True)

def strip_bound(S,a):
    p=ctx.prec
    ctx.prec=128
    try:
        # By f(-theta)=f(theta), f(pi-theta)=f(theta), it suffices
        # to cover [0,pi/2] x [-a,a]. Boxes enclose the closed strip.
        todo=[(arb(1)/2,arb(1)/2,0)]
        M=arb(0)
        boxes=0
        quarter=arb.pi()/2
        while todo:
            c,h,d=todo.pop()
            z=acb(arb(c*quarter,h*quarter),arb(0,a))
            w=f(acb(S),z)
            if w.is_finite():
                b=abs(w).upper()
                if b.is_finite():
                    M=b if b>M else M
                    boxes+=1
                    continue
            if d>=16:
                return None,boxes
            h=h/2
            todo.extend(((c-h,h,d+1),(c+h,h,d+1)))
        assert M>0
        return M,boxes
    finally:
        ctx.prec=p

def periodic(S,goal):
    p=ctx.prec
    # Test analyticity; shrink the strip if interval overestimation or
    # a singularity prevents a successful finite analytic enclosure.
    a=arb(1)/2
    M=None
    for i in range(15):
        M,boxes=strip_bound(S,a)
        if M is not None:
            break
        a=a/2
    assert M is not None, 'No verified analytic strip'
    # N=4*m. Optimize N with the actual rigorous error formula.
    # A dyadic strip width is exact; avoid floating-point decisions.
    k=int((arb(goal+32)*arb(2).log()/a).ceil().unique_fmpz())
    N=4*((k+3)//4)
    tail=S*S*M/((a*N).expm1())
    while not tail < arb(2)**(-goal):
        N+=4
        tail=S*S*M/((a*N).expm1())
    m=N//4
    print('PERIODIC STRIP',S.str(10),'bits',p,'width',a.str(10),
          'boxes',boxes,'N',N,'quadrant nodes',m+1,flush=True)
    assert m<=200000, 'pilot node cap; no unbounded full run'
    # By exact quadrant symmetries the full N-node sum is
    # 2*f(0) + 4*sum_{j=1}^{m-1}f(j*pi/(2m)) + 2*f(pi/2).
    # f(pi/2)=0 exactly. Online summation uses constant storage.
    s0=f(acb(S),acb(0))
    assert s0.is_finite() and s0.imag.contains(0)
    total=2*s0.real
    step=arb.pi()/(2*m)
    for j in range(1,m):
        v=f(acb(S),acb(j*step))
        assert v.is_finite() and v.imag.contains(0), ('node',j)
        total+=4*v.real
    out=S*S*total/(2*N)+arb(0,tail.upper())
    assert out.is_finite() and out>0
    assert out.rel_accuracy_bits()>=p-100, ('accuracy',out.rel_accuracy_bits())
    return out

def benchmark(S,p):
    ctx.prec=p
    t0=time.monotonic()
    ref=integrals(S)
    baseline=time.monotonic()-t0
    t0=time.monotonic()
    v=periodic(S,p-48)
    duration=time.monotonic()-t0
    assert ref.overlaps(v), ('reference mismatch',S,p)
    print('PERIODIC BENCHMARK PASS',S.str(10),'bits',p,
          'reference',baseline,'periodic',duration,
          'reference bits',ref.rel_accuracy_bits(),
          'periodic bits',v.rel_accuracy_bits(),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('S',type=int,choices=[4,93])
    ap.add_argument('--bits',type=int,choices=[256,512,1024,4096],default=512)
    ns=ap.parse_args()
    benchmark(arb(ns.S),ns.bits)
