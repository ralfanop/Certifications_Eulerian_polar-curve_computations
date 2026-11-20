#!/usr/bin/env python3
"""Independent M12 validated Taylor-Cauchy quadrature benchmark.

For each dyadic panel [c-h,c+h], set u=c+h*v.  If the analytically
flagged complex-ball evaluation on the box |Re(v)|,|Im(v)| <= R
is finite, it bounds the analytic integrand on the closed disk |v|<=R.
For its Taylor coefficients a_k, Cauchy gives |a_k|<=M/R**k.
The integral of the truncated series is h*sum_even 2*a_k/(k+1);
a rigorous absolute remainder is <=2*h*M*R**(-N)/(1-1/R).
All constants and coefficients are FLINT/Arb balls, not floats.
The series implementation computes the same regularized integrand as
the reference, using direct exponential quotients only at nonzero
Taylor centers. At those centers all denominators are verified nonzero.
This is a bounded benchmark, NOT a million-decimal certificate.
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

def panel_integral(S,high,derivative,goal):
    # Split only when the analyticity/finite-bound test does not pass.
    todo=[(arb(1)/2,arb(1)/2,0)]
    out=arb(0)
    panels=largest=0
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
        # Uniform absolute error budget: sum h over all panels is 1/2.
        # Set the truncation length by the *verified* tail bound.
        q=arb(1)/R
        N=max(2,(goal+32)//(2 if R==4 else 1))
        tail=2*h*M*q**N/(1-q)
        while not tail<h*arb(2)**(-goal-4):
            N+=32
            tail=2*h*M*q**N/(1-q)
        assert N<=32768, ('benchmark memory gate',N)
        coeff=series_callback(S,c,h,N,high,derivative)
        assert len(coeff)<=N and all(x.is_finite() for x in coeff)
        terms=[2*coeff[k]/(k+1) for k in range(0,len(coeff),2)]
        # Balanced summation of the exact integral of the truncated series.
        while len(terms)>1:
            terms=[terms[k]+terms[k+1] if k+1<len(terms) else terms[k]
                   for k in range(0,len(terms),2)]
        v=h*(terms[0] if terms else arb(0))
        out+=v+arb(0,tail.upper())
        panels+=1
        largest=max(largest,N)
    print('TAYLOR PANELS', 'high' if high else 'low','derivative',derivative,
          'panels',panels,'max degree',largest-1,flush=True)
    return out

def integral_taylor(S,derivative=False):
    goal=ctx.prec-48
    v=sum(panel_integral(S,high,derivative,goal) for high in (False,True))/arb.pi()
    if derivative:
        a=A(acb(S)).real
        v*=a*(1/(S*S)-S.exp()/S.expm1()**2)
        assert v>0
    assert v.is_finite() and v.rel_accuracy_bits()>=ctx.prec-100, ('Taylor accuracy',v.rel_accuracy_bits())
    return v

def benchmark(S,P):
    ctx.prec=P
    for derivative in (False,True):
        start=time.monotonic()
        v=integrals(S,derivative)
        old=time.monotonic()-start
        start=time.monotonic()
        w=integral_taylor(S,derivative)
        new=time.monotonic()-start
        assert v.overlaps(w), ('reference overlap',S,derivative)
        print('TAYLOR BENCHMARK PASS',S,'bits',P,'derivative',derivative,
              'baseline seconds',old,'Taylor seconds',new,'speedup',old/new,
              'baseline bits',v.rel_accuracy_bits(),'Taylor bits',w.rel_accuracy_bits(),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('S',type=int,choices=[4,93])
    p.add_argument('--bits',type=int,choices=[512,1024,4096,8192],default=1024)
    a=p.parse_args()
    benchmark(arb(a.S),a.bits)
