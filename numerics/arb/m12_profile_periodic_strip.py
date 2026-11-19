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
from m12_profile_interval_newton import A, exprel, integrals, initial, printed_check, ROWS
from fractions import Fraction as Q
import json
from pathlib import Path
from million_decimal_common import exact

def B(S,s):
    a=A(S)
    delta=S-s
    # Direct quotient away from the endpoint; stable removable quotient
    # near the endpoint. Both formulas are mathematically identical.
    if abs(delta).lower() > abs(S).upper()/8:
        return (a-A(s))/delta
    return 1/(S*s)-s.exp()*exprel(delta)/(S.expm1()*s.expm1())

def f(S,theta,derivative=False):
    s=S*theta.sin()
    c=theta.cos()
    root=(B(S,s)*B(S,-s)).sqrt(analytic=True)
    return 1/root if derivative else c*c*root

def strip_bound(S,a,derivative=False):
    p=ctx.prec
    ctx.prec=128
    try:
        # By f(-theta)=f(theta), f(pi-theta)=f(theta), it suffices
        # to cover [0,pi/2] x [-a,a]. Boxes enclose the closed strip.
        # Split both coordinates: retaining the entire vertical radius
        # in every box severely overestimates the analytic range.
        todo=[(arb(1)/2,arb(1)/2,arb(0),arb(1),0)]
        M=arb(0)
        boxes=visited=0
        quarter=arb.pi()/2
        while todo:
            c,h,y,k,d=todo.pop()
            visited+=1
            if visited>80000:
                return None,boxes
            z=acb(arb(c*quarter,h*quarter),arb(y*a,k*a))
            w=f(acb(S),z,derivative)
            if w.is_finite():
                b=abs(w).upper()
                if b.is_finite():
                    M=b if b>M else M
                    boxes+=1
                    continue
            if d>=30:
                return None,boxes
            if h*quarter>k*a:
                h=h/2
                todo.extend(((c-h,h,y,k,d+1),(c+h,h,y,k,d+1)))
            else:
                k=k/2
                todo.extend(((c,h,y-k,k,d+1),(c,h,y+k,k,d+1)))
        assert M>0
        return M,boxes
    finally:
        ctx.prec=p

def periodic(S,goal,derivative=False):
    p=ctx.prec
    # Test analyticity; shrink the strip if interval overestimation or
    # a singularity prevents a successful finite analytic enclosure.
    a=arb(1)/2
    while S*a>3:
        a=a/2
    M=None
    for i in range(15):
        M,boxes=strip_bound(S,a,derivative)
        if M is not None:
            break
        a=a/2
    assert M is not None, 'No verified analytic strip'
    # N=4*m. Optimize N with the actual rigorous error formula.
    # A dyadic strip width is exact; avoid floating-point decisions.
    k=int((arb(goal+32)*arb(2).log()/a).ceil().unique_fmpz())
    N=4*((k+3)//4)
    aS=arb(1)/2+1/S.expm1()-1/S
    aprime=1/(S*S)-S.exp()/S.expm1()**2
    assert aS>0 and aprime>0
    scale=aS*aprime if derivative else S*S
    tail=scale*M/((a*N).expm1())
    while not tail < arb(2)**(-goal):
        N+=4
        tail=scale*M/((a*N).expm1())
    m=N//4
    print('PERIODIC STRIP',S.str(10),'bits',p,'width',a.str(10),
          'boxes',boxes,'N',N,'quadrant nodes',m+1,flush=True)
    assert m<=500000, 'pilot node cap; no unbounded full run'
    # By exact quadrant symmetries the full N-node sum is
    # 2*f(0) + 4*sum_{j=1}^{m-1}f(j*pi/(2m)) + 2*f(pi/2).
    # f(pi/2)=0 exactly. Online summation uses constant storage.
    # At the strictly interior real nodes cos(theta)>0, so the
    # original factorization simplifies to f=cos(theta)*sqrt(aS^2-A(s)^2)/S.
    # Evaluate A(S) once, use a single real expm1 per node; the
    # strip certificate above still concerns the identical analytic f.
    # H'(S)=A(S)A'(S)/2 times the periodic mean of 1/sqrt(C).
    # At theta=pi/2 the continuous g-value is sqrt(S/(A(S)A'(S))).
    total=2*(S/aS+(S/(aS*aprime)).sqrt()) if derivative else 2*aS/S
    step=arb.pi()/(2*m)
    for j in range(1,m):
        theta=j*step
        s=S*theta.sin()
        c=theta.cos()
        assert s>0 and c>0
        v=arb(1)/2+1/s.expm1()-1/s
        rad=aS*aS-v*v
        assert rad>0, ('node square root',j)
        total+=4*S*c/rad.sqrt() if derivative else 4*c*rad.sqrt()/S
    out=scale*total/(2*N)+arb(0,tail.upper())
    assert out.is_finite() and out>0
    assert out.rel_accuracy_bits()>=goal-20, ('accuracy',out.rel_accuracy_bits(),goal)
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

def root_pilot(row,P):
    # A certified initial bracket; every following interval Newton
    # inclusion uses H'(X) for ALL S in X, not a point derivative.
    X=initial(row,256)
    target=Q(row)
    for iteration in range(32):
        b=X.rel_accuracy_bits()
        ctx.prec=max(128,b+96)
        D=periodic(X,max(32,b-48),True)
        assert D>0 and D.rel_accuracy_bits()>=b-100
        ctx.prec=min(P,max(384,2*b+96))
        m=X.mid()
        H=periodic(m,ctx.prec-48)
        Y=m-(H-exact(target))/D
        assert Y.is_finite() and Y>0
        new=X.intersection(Y)
        assert new.rel_accuracy_bits()>b
        X=new
        F=A(acb(X)).real**2/4
        print('PERIODIC ROOT',row,'working',ctx.prec,'root bits',X.rel_accuracy_bits(),
              'profile bits',F.rel_accuracy_bits(),flush=True)
        if F.rel_accuracy_bits()>=P-128:
            ctx.prec=P
            F=A(acb(X)).real**2/4
            printed_check(row,F)
            assert F.rel_accuracy_bits()>=P-128
            Path('m12-periodic-pilot-'+row.replace('/','-')+'.json').write_text(json.dumps(
                dict(t=row,working_bits=P,relative_bits=F.rel_accuracy_bits(),
                     lower=str(F.lower().fmpq()),upper=str(F.upper().fmpq()),
                     root_lower=str(X.lower().fmpq()),root_upper=str(X.upper().fmpq()),
                     scope='intermediate precision only'))+'\n')
            print('PERIODIC ROOT PILOT SUCCESS',row,'bits',P,'relative',F.rel_accuracy_bits(),flush=True)
            return
    raise RuntimeError('root refinement did not reach target')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('S',nargs='?',type=int,choices=[4,93])
    ap.add_argument('--row',choices=ROWS)
    ap.add_argument('--bits',type=int,choices=[256,512,1024,4096,8192,16384],default=512)
    ns=ap.parse_args()
    if ns.row:
        assert ns.bits in (4096,8192,16384)
        root_pilot(ns.row,ns.bits)
    else:
        assert ns.S is not None
        benchmark(arb(ns.S),ns.bits)
