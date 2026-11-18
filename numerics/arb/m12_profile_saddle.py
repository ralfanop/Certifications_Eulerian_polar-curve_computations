#!/usr/bin/env python3
"""M12 Table 1 validated saddle-variable quadrature. Authoritative ZIP SHA256
7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860.
Pilot and full runs are distinct. A precision setting alone is not evidence.

A(s)=Lambda'(s). Integration by parts, then x=A(s), gives
Phi(A(S))=1/pi * integral_0^S sqrt(A(S)^2-A(s)^2) ds.
a' > 0; differentiating this integral gives its S derivative.
Split at S/2 and substitute s=S-(S/2)u^2 on the upper half.
The difference quotient B=(A(S)-A(s))/(S-s) is evaluated without
division by S-s. The factored square root is positive for real u.
Arb complex quadrature is used with the analytic flag respected.
Only endpoint sign inequalities, not Newton iterates, certify the root.
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

def integrals(S, derivative=False):
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
    tol=arb(2)**(-max(32,p-(60000 if p>100000 else 24)))
    result=sum(acb.integral(f,0,1,rel_tol=tol,abs_tol=tol,
                            eval_limit=2000000) for f in (low,high))/arb.pi()
    assert result.is_finite() and result.imag.contains(0), ('quadrature', p, S.str(20))
    if derivative:
        aprime=1/(Sc*Sc)-Sc.exp()/(es*es)
        result*=a*aprime
        assert result.imag.contains(0) and result.real > 0
    ans=result.real
    assert ans.rel_accuracy_bits() >= max(20,p-(80000 if p>100000 else 45)), ('accuracy',p,ans.rel_accuracy_bits())
    return ans

def solve(row, full):
    P=WORK if full else 256
    target=Q(row)
    # Printed digits are only candidate generation. Final interval
    # tests check the printed cell and independent strict root signs.
    ctx.prec=64
    a0=2*exact(Q(ROWS[row])).sqrt()
    S=(12*a0/(1-4*a0*a0)).mid()
    p=64
    while True:
        ctx.prec=p
        for _ in range(9 if p==64 else 3):
            h=integrals(S)
            dh=integrals(S,True)
            step=(h-exact(target))/dh
            nxt=(S-step).mid()
            if not nxt>0:
                nxt=(S/2).mid()
            S=nxt
        print('candidate',row,'bits',p,'S',S.str(20),flush=True)
        if p==P: break
        p=min(2*p,P)
    radius=arb(2)**(-(P-(120000 if full else 64)))
    lo,hi=S-radius,S+radius
    assert 0<lo<hi
    lval,hval=integrals(lo),integrals(hi)
    assert lval<exact(target)<hval, ('root signs', row, lval.str(20), hval.str(20))
    ball=arb(S,2*radius)
    assert ball.lower()<=lo.lower() and hi.upper()<=ball.upper()
    F=(A(acb(ball)).real)**2/4
    assert F.is_finite() and F>0
    d=Q(ROWS[row])
    unit=Q(1,10**7)
    assert exact(d-unit/2)<F<exact(d+unit/2), ('printed cell', row,F.str(20))
    print('PROFILE',row,'relative bits',F.rel_accuracy_bits(),F.str(20),flush=True)
    if full:
        assert ctx.prec==WORK and F.rel_accuracy_bits()>=MIN
        record('tab:ul-beta F('+row+')',F)
        finish('m12-profile-'+row.replace('/','-'))
    else:
        assert F.rel_accuracy_bits() >= 160
        print('PILOT PASS: not a million-decimal certificate',flush=True)
    path=Path('m12-profile-'+row.replace('/','-')+'.json')
    path.write_text(json.dumps({'t':row,'working_bits':P,'relative_bits':F.rel_accuracy_bits(),
                      'lower':str(F.lower().fmpq()),'upper':str(F.upper().fmpq())})+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('row',choices=ROWS)
    ap.add_argument('--full',action='store_true')
    ns=ap.parse_args()
    solve(ns.row,ns.full)
