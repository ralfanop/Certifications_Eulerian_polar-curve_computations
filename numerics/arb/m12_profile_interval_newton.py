#!/usr/bin/env python3
"""M12 alternative interval-Newton refinement of #385.
Given X containing the unique root of H(S)=t, the mean value theorem
gives root in m-(H(m)-t)/H'(X), m=mid(X), provided 0 not in H'(X).
Compute H'(X) with fewer bits than H(m); its enclosure is uniform in S in X:
the analytic quadrature callback encloses the regularized integrand and
derivative for every S in X, with the analytic flag respected. Intersect
with X. No heuristic iterate is accepted as a certificate.
Author ZIP SHA256 7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860.
"""
from flint import arb, acb, ctx
from million_decimal_common import WORK, MIN, exact, record, finish
from fractions import Fraction as Q
from pathlib import Path
import json
import argparse

ROWS = {'1/4':'0.0178432','1/2':'0.0303768','1':'0.0445361',
        '2':'0.0548091','4':'0.0598372'}

def A(s):
    # At zero the quotient is removable. This entire hypergeometric
    # numerator and denominator evaluate the same meromorphic function.
    if s.contains(0):
        w = s*s/16
        return s/12*w.hypgeom_0f1(2.5)/w.hypgeom_0f1(1.5)
    return acb(1)/2 + 1/s.expm1() - 1/s

def exprel(z):
    if z.contains(0):
        return z.hypgeom_1f1(1,2)
    return z.expm1()/z

import time
def integrals(S, derivative=False, goal=None):
    Sc=acb(S)
    a=A(Sc)
    es=Sc.expm1()
    half=Sc/2
    def low(u, analytic):
        s=half*u
        r=(a*a-A(s)**2).sqrt(analytic=analytic)
        return half/r if derivative else half*r
    def high(u, analytic):
        s=Sc-half*u*u
        delta=half*u*u
        B=1/(Sc*s)-s.exp()*exprel(delta)/(es*s.expm1())
        r=(half*B*(a+A(s))).sqrt(analytic=analytic)
        return Sc/r if derivative else Sc*u*u*r
    p=ctx.prec
    tol=arb(2)**(-max(32, p-(60000 if p>100000 else 24)) if goal is None else -goal)
    result=sum(acb.integral(f,0,1,rel_tol=tol,abs_tol=tol,
                            eval_limit=2000000) for f in (low,high))/arb.pi()
    assert result.is_finite() and result.imag.contains(0), ('quadrature', p, S.str(20))
    if derivative:
        aprime=1/(Sc*Sc)-Sc.exp()/(es*es)
        result*=a*aprime
        assert result.imag.contains(0) and result.real > 0
    ans=result.real
    if goal is None:
        assert ans.rel_accuracy_bits() >= max(20,p-(80000 if p>100000 else 45)), ('accuracy',p,ans.rel_accuracy_bits())
    return ans


def initial(row,P):
    # Original #385 exact-endpoint-sign method; returns actual root ball.
    target=Q(row)
    ctx.prec=64
    a0=2*exact(Q(ROWS[row])).sqrt()
    S=(12*a0/(1-4*a0*a0)).mid()
    p=64
    while True:
        ctx.prec=p
        for _ in range(9 if p==64 else 3):
            h=integrals(S); dh=integrals(S,True)
            nxt=(S-(h-exact(target))/dh).mid()
            S=nxt if nxt>0 else (S/2).mid()
        if p==P: break
        p=min(2*p,P)
    radius=arb(2)**(-(P-64))
    lo,hi=S-radius,S+radius
    assert 0<lo<hi
    assert integrals(lo)<exact(target)<integrals(hi)
    X=arb(S,2*radius)
    assert X.lower()<=lo.lower() and hi.upper()<=X.upper()
    return X

def refine(row,P):
    X=initial(row,256)
    goal=MIN+32 if P==WORK else P-100
    for iteration in range(40):
        b=X.rel_accuracy_bits()
        # Derivative interval must cover every S in the current ball.
        # Its absolute tolerance is looser than parameter uncertainty.
        ctx.prec=max(128,b+96)
        D=integrals(X,True,goal=max(40,b-48))
        assert D.is_finite() and D>0
        dacc=D.rel_accuracy_bits()
        assert dacc>=b-100, ('derivative enclosure too wide',b,dacc)
        # At a point m (exact dyadic), use one high-precision integral.
        p=min(P,max(b*2+96,384))
        ctx.prec=p
        m=X.mid()
        h=integrals(m)
        Y=m-(h-exact(Q(row)))/D
        assert Y.is_finite() and Y>0
        Z=X.intersection(Y)
        new=Z.rel_accuracy_bits()
        assert new>b, ('interval Newton failed to contract',b,new)
        X=Z
        F=A(acb(X)).real**2/4
        acc=F.rel_accuracy_bits()
        print('INTERVAL NEWTON',row,'p',p,'derivative bits',dacc,'root bits',new,'F bits',acc,flush=True)
        if acc>=goal: return X,F
    raise RuntimeError('refinement iteration limit')

def printed_check(row,F):
    d=Q(ROWS[row]); unit=Q(1,10**7)
    assert F.is_finite() and F>0
    assert exact(d-unit/2)<F<exact(d+unit/2)

def benchmark(row,P):
    t=time.monotonic()
    old=initial(row,P)
    oldF=A(acb(old)).real**2/4
    oldtime=time.monotonic()-t
    t=time.monotonic()
    new,newF=refine(row,P)
    newtime=time.monotonic()-t
    printed_check(row,oldF); printed_check(row,newF)
    assert old.overlaps(new) and oldF.overlaps(newF)
    assert oldF.rel_accuracy_bits()>=P-120
    assert newF.rel_accuracy_bits()>=P-100
    print('BENCHMARK PASS',row,P,'baseline seconds',oldtime,'interval newton seconds',newtime,
          'speedup',oldtime/newtime,'baseline bits',oldF.rel_accuracy_bits(),
          'new bits',newF.rel_accuracy_bits(),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('row',choices=ROWS)
    ap.add_argument('--bits',type=int,default=2048)
    ap.add_argument('--full',action='store_true')
    ns=ap.parse_args()
    if ns.full:
        X,F=refine(ns.row,WORK)
        ctx.prec=WORK
        F=A(acb(X)).real**2/4
        printed_check(ns.row,F)
        record('tab:ul-beta F('+ns.row+') interval-newton',F)
        finish('m12-profile-interval-newton-'+ns.row.replace('/','-'))
        Path('m12-profile-'+ns.row.replace('/','-')+'.json').write_text(json.dumps(
            {'t':ns.row,'working_bits':WORK,'relative_bits':F.rel_accuracy_bits(),
             'lower':str(F.lower().fmpq()),'upper':str(F.upper().fmpq())})+'\n')
    else:
        assert 512<=ns.bits<=16384
        benchmark(ns.row,ns.bits)
