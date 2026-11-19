#!/usr/bin/env python3
"""Independent M12 rigorous Clenshaw-Curtis/FFT quadrature pilot.

On a panel [c-h,c+h], write g(x)=f(c+h*x). A finite analytic
complex-ball evaluation on the rectangular hull of the Bernstein
ellipse E_rho proves |g| <= M there. Its Chebyshev coefficients
satisfy |a_k| <= 2 M rho**(-k), k>=1 (Laurent/Cauchy estimate).

At the n+1 cosine nodes, T_k aliases to T_m with 0<=m<=n
(m=min(k mod 2n,2n-(k mod 2n))). Integrating that interpolation
exactly gives a quadrature exact on degrees <=n; for every T_k,
the error is at most 4 on [-1,1], since |T_k|, |T_m| <= 1.
Consequently the absolute panel error is bounded by
8*h*M*rho**(-n-1)/(1-1/rho). No float estimates or heuristic
agreement enter the certified error. The FFT in Arb encloses the
weights of the exact rule; symmetry halves node evaluations.

Benchmark only: bounded degrees and precision, not a full-million
digit certificate. Author ZIP SHA256 as recorded in #385/#390.
"""
import argparse
from functools import lru_cache
from time import monotonic
from flint import arb, acb, ctx
from m12_profile_interval_newton import A, exprel, integrals


def callback(S, high, derivative):
    Sc=acb(S)
    a=A(Sc)
    half=Sc/2
    es=Sc.expm1()
    if not high:
        def f(u, analytic):
            r=(a*a-A(half*u)**2).sqrt(analytic=analytic)
            return half/r if derivative else half*r
    else:
        def f(u, analytic):
            delta=half*u*u
            s=Sc-delta
            B=1/(Sc*s)-s.exp()*exprel(delta)/(es*s.expm1())
            r=(half*B*(a+A(s))).sqrt(analytic=analytic)
            return Sc/r if derivative else Sc*u*u*r
    return f


def ellipse_bound(S,c,h,high,derivative,rho):
    """Cover the ellipse by dyadic subboxes, not a single dependency-heavy box.

    Normalized coordinates (x,y) satisfy x*x+y*y<=1. Discard a tile
    only when its exact minimum squared distance from 0 exceeds 1.
    Every retained leaf must certify analyticity by the original
    flagged callback; the maximum of the leaf magnitude bounds then
    bounds the whole closed ellipse. A failed cover is a rejection,
    never an underestimated bound.
    """
    p=ctx.prec
    ctx.prec=128
    try:
        a=h*(arb(rho)+1/arb(rho))/2
        b=h*(arb(rho)-1/arb(rho))/2
        f=callback(S,high,derivative)
        todo=[(arb(0),arb(0),arb(1),0)]
        M=arb(0)
        while todo:
            x,y,d,depth=todo.pop()
            dx=max(arb(0),abs(x)-d)
            dy=max(arb(0),abs(y)-d)
            if dx*dx+dy*dy>1:
                continue
            z=acb(arb(c+a*x,(a*d).upper()),arb(b*y,(b*d).upper()))
            val=f(z,True)
            if val.is_finite():
                M=max(M,abs(val).upper())
            elif depth<4:
                dd=d/2
                todo.extend((x+i*dd,y+j*dd,dd,depth+1)
                            for i in (-1,1) for j in (-1,1))
            else:
                return None
        return M if M.is_finite() else None
    finally:
        ctx.prec=p


def mu(k):
    return arb(0) if k%2 else arb(2)/(1-k*k)


@lru_cache(maxsize=4)
def rule(n,precision):
    assert ctx.prec==precision
    length=2*n
    # Inverse DFT includes 1/(2n). The vector of exact moments is
    # symmetric, so either sign convention yields the same weights.
    weights=acb.dft([acb(mu(min(k,length-k))) for k in range(length)],
                    inverse=True)
    root=acb(arb(1)/n).exp_pi_i()
    z=acb(1)
    nodes=[]
    for j in range(n+1):
        x=arb(1) if j==0 else (-arb(1) if j==n else z.real)
        assert weights[j].imag.contains(0)
        w=weights[j].real*(1 if j in (0,n) else 2)
        assert w.is_finite() and x.is_finite()
        nodes.append((x,w))
        z*=root
    assert sum(w for x,w in nodes).contains(2)
    return nodes


def polynomial_test():
    n=16
    nodes=rule(n,ctx.prec)
    for k in range(n+1):
        val=sum(w*x**k for x,w in nodes)
        expected=arb(0) if k%2 else arb(2)/(k+1)
        assert val.overlaps(expected)
    print('CC FFT POLYNOMIAL TEST PASS',flush=True)


def part(S,high,derivative,goal):
    todo=[(arb(1)/2,arb(1)/2,0)]
    f=callback(S,high,derivative)
    result=arb(0)
    panels=maxdegree=0
    while todo:
        c,h,depth=todo.pop()
        M=None
        for rho in (8,4,2):
            M=ellipse_bound(S,c,h,high,derivative,rho)
            if M is not None and M.is_finite():
                break
            M=None
        if M is None:
            assert depth<24, ('ellipse failure',S,c,h)
            hh=h/2
            todo.extend(((c-hh,hh,depth+1),(c+hh,hh,depth+1)))
            continue
        r=arb(rho)
        n=2
        error=8*h*M*r**(-n-1)/(1-1/r)
        while not error < h*arb(2)**(-goal-4):
            n*=2
            error=8*h*M*r**(-n-1)/(1-1/r)
        assert n<=16384, ('benchmark memory gate',n)
        val=arb(0)
        for x,w in rule(n,ctx.prec):
            y=f(acb(c+h*x),False)
            assert y.is_finite() and y.imag.contains(0)
            val+=w*y.real
        result+=h*val+arb(0,error.upper())
        panels+=1
        maxdegree=max(maxdegree,n)
    print('CC PANELS','high' if high else 'low','derivative',derivative,
          'panels',panels,'maxdegree',maxdegree,flush=True)
    return result


def integral_cc(S,derivative=False):
    p=ctx.prec
    ctx.prec=p+96
    try:
        out=sum(part(S,high,derivative,p-48) for high in (False,True))/arb.pi()
        if derivative:
            a=A(acb(S)).real
            out*=a*(1/(S*S)-S.exp()/S.expm1()**2)
            assert out>0
        assert out.is_finite() and out.rel_accuracy_bits()>=p-100, (
            'CC accuracy',p,out.rel_accuracy_bits())
        return out
    finally:
        rule.cache_clear()
        ctx.prec=p


def benchmark(S,P):
    ctx.prec=P
    polynomial_test()
    rule.cache_clear()
    for derivative in (False,True):
        start=monotonic()
        candidate=integral_cc(S,derivative)
        fast=monotonic()-start
        start=monotonic()
        baseline=integrals(S,derivative)
        old=monotonic()-start
        assert baseline.overlaps(candidate), ('reference mismatch',S,derivative)
        print('CC BENCHMARK PASS',S,'bits',P,'derivative',derivative,
              'baseline seconds',old,'CC seconds',fast,'speedup',old/fast,
              'baseline bits',baseline.rel_accuracy_bits(),
              'CC bits',candidate.rel_accuracy_bits(),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('S',type=int,choices=[4,93])
    p.add_argument('--bits',type=int,choices=[512,2048,8192],default=512)
    a=p.parse_args()
    benchmark(arb(a.S),a.bits)
