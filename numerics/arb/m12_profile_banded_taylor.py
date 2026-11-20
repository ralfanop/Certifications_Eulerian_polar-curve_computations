#!/usr/bin/env python3
"""M12 bounded precision-banded Taylor-Cauchy pilot.

Reuses the endpoint-regularized callbacks and disk test from PR #413.
If g(v)=f(c+R*h*v) has |g|<=M on |v|<=1, Cauchy gives |b_k|<=M.
Integrate f(c+h*u)=sum b_k*u^k/R^k. Coefficients with large k
have exponentially small weights R^-k, so compute successive bands
with progressively fewer working bits. Every coefficient and sum is
an Arb enclosure; no precision estimate is used as a proof of accuracy.
The omitted tail is bounded by 2*h*M*R^-N/(1-1/R).
Benchmark only; no million-digit claims or unrestricted memory jobs.
"""
import argparse
import time
from flint import arb, acb, arb_series, ctx
from m12_profile_interval_newton import A, exprel, integrals

def complex_callback(S, u, high, derivative):
    S=acb(S)
    a=A(S)
    half=S/2
    if not high:
        r=(a*a-A(half*u)**2).sqrt(analytic=True)
        return half/r if derivative else half*r
    s=S-half*u*u
    delta=half*u*u
    B=1/(S*s)-s.exp()*exprel(delta)/(S.expm1()*s.expm1())
    r=(half*B*(a+A(s))).sqrt(analytic=True)
    return S/r if derivative else S*u*u*r

def series_A(s):
    assert s[0]!=0 and not s[0].contains(0)
    e=s.exp()-1
    assert not e[0].contains(0)
    return arb_series([arb(1)/2])+1/e-1/s

def series_callback(S,c,h,N,high,derivative):
    old=ctx.cap
    ctx.cap=N
    try:
        u=arb_series([c,h])
        a=A(acb(S)).real
        half=S/2
        if not high:
            r=(arb_series([a*a])-series_A(u*half)**2).sqrt()
            return (arb_series([half])/r if derivative else r*half).coeffs()
        delta=u*u*half
        s=arb_series([S])-delta
        assert not delta[0].contains(0)
        ds=delta.exp()-1
        es=s.exp()-1
        assert not es[0].contains(0)
        B=1/(s*S)-s.exp()*(ds/delta)/(es*S.expm1())
        r=(B*(series_A(s)+a)*half).sqrt()
        return (arb_series([S])/r if derivative else u*u*r*S).coeffs()
    finally:
        ctx.cap=old

def disk_bound(S,c,h,high,derivative,R):
    p=ctx.prec
    ctx.prec=128
    try:
        z=acb(arb(c,R*h),arb(0,R*h))
        v=complex_callback(S,z,high,derivative)
        if not v.is_finite(): return None
        M=abs(v).upper()
        if not M.is_finite(): return None
        return M
    finally:
        ctx.prec=p


import resource

def band_panel(S,c,h,N,high,derivative,R,bands,goal):
    P=ctx.prec
    acc=arb(0)
    lg=1 if R==2 else 2
    stats=[]
    retries=0
    # In the normalized panel [-1,1], allocate a strict absolute
    # radius budget to each band. Multiplication by h happens afterwards.
    # Cauchy bounds coefficient magnitudes, not the rounding errors of
    # the internal series arithmetic; the attenuation heuristic is only
    # a starting precision, never an accuracy guarantee.
    tol=arb(2)**(-goal-8)/bands
    cap=4*P+256
    for i in range(bands):
        lo=N*i//bands
        hi=N*(i+1)//bands
        if hi<=lo: continue
        q=max(128,P-lg*lo+64)
        while True:
            b=None
            try:
                ctx.prec=q
                b=series_callback(S,c,R*h,hi,high,derivative)
                if len(b)>hi or not all(x.is_finite() for x in b):
                    b=None
            except (AssertionError, ValueError, ZeroDivisionError):
                # A low-precision enclosure may cross a pole or cut.
                # Retry at a greater precision; never accept it.
                b=None
            finally:
                ctx.prec=P
            if b is not None:
                value=arb(0)
                for k in range(lo+(lo%2),hi,2):
                    if k<len(b):
                        value+=2*b[k]*arb(2)**(-lg*k)/(k+1)
                if value.is_finite() and value.rad() < tol:
                    acc+=value*h
                    stats.append((hi,q))
                    break
            del b
            if q>=cap:
                raise ArithmeticError(('band radius budget not met at cap',
                    lo,hi,q,goal,high,derivative))
            q=min(cap,q+max(64,q//2))
            retries+=1
    return acc,stats,retries

def panel_integral(S,high,derivative,goal,bands):
    todo=[(arb(1)/2,arb(1)/2,0)]
    out=arb(0)
    panels=largest=peak=max_q=retries=0
    while todo:
        c,h,depth=todo.pop()
        M=None
        for R in (4,2):
            M=disk_bound(S,c,h,high,derivative,R)
            if M is not None: break
        if M is None:
            assert depth<24, ('analytic disk failure',S,c,h)
            h=h/2
            todo.extend(((c-h,h,depth+1),(c+h,h,depth+1)))
            continue
        q=arb(1)/R
        N=max(2,(goal+32)//(2 if R==4 else 1))
        tail=2*h*M*q**N/(1-q)
        while not tail<h*arb(2)**(-goal-4):
            N+=32
            tail=2*h*M*q**N/(1-q)
        assert N<=32768, ('bounded pilot degree cap',N)
        v,stats,nretry=band_panel(S,c,h,N,high,derivative,R,bands,goal)
        retries+=nretry
        max_q=max(max_q,max(p for n,p in stats))
        out+=v+arb(0,tail.upper())
        panels+=1
        largest=max(largest,N)
        peak=max(peak,max(n*p for n,p in stats))
    print('BANDED PANELS',high,derivative,'panels',panels,'max degree',
          largest-1,'max coefficient-bit product',peak,'max working bits',max_q,
          'precision retries',retries,flush=True)
    return out

def integral_banded(S,derivative,bands):
    goal=ctx.prec-48
    v=sum(panel_integral(S,high,derivative,goal,bands) for high in (False,True))/arb.pi()
    if derivative:
        a=A(acb(S)).real
        v*=a*(1/(S*S)-S.exp()/S.expm1()**2)
    assert v.is_finite() and v>0
    assert v.rel_accuracy_bits()>=ctx.prec-100, ('band accuracy',v.rel_accuracy_bits())
    return v

def main():
    p=argparse.ArgumentParser()
    p.add_argument('S',type=int,choices=[4,93])
    p.add_argument('--bits',type=int,choices=[512,2048,8192,16384],default=2048)
    p.add_argument('--bands',type=int,choices=[1,4,8],default=4)
    p.add_argument('--derivative',action='store_true')
    a=p.parse_args()
    ctx.prec=a.bits
    S=arb(a.S)
    start=time.monotonic()
    v=integral_banded(S,a.derivative,a.bands)
    elapsed=time.monotonic()-start
    peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print('BANDED RESULT',a.S,'bits',a.bits,'bands',a.bands,'derivative',
          a.derivative,'relative bits',v.rel_accuracy_bits(),'seconds',elapsed,
          'peak RSS KiB',peak,flush=True)
    # Reference is independent validated quadrature; cap its precision at
    # 2048 for the largest pilots, not a full-precision cross-check there.
    ctx.prec=min(a.bits,2048)
    ref=integrals(S,a.derivative)
    assert ref.overlaps(v), ('reference mismatch',a.S,a.bits)
    print('BANDED TAYLOR PILOT SUCCESS',a.S,a.bits,a.bands,a.derivative,
          'reference bits',ref.rel_accuracy_bits(),flush=True)

if __name__=='__main__':
    main()
