#!/usr/bin/env python3
"""Final M12 Table 1: exact scaled uniform moments, symmetric monic recurrence.
Authoritative ZIP SHA256 7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860.

For X=2S_M/M, its MGF is (sinh(t/M)/(t/M))^M. Hence
mu_(2k) = (2k)! sum_j (-1)^j binom(M,j)(M-2j)^(2k+M) /
          (2^M M^(2k) (2k+M)!).
All numerator/denominator calculations are exact FLINT integers.
The monic Chebyshev recurrence evaluates moment inner products in Arb.
Orthogonality by parity eliminates every odd mixed moment. Strict
positive norms and the final enclosing intervals are asserted.
"""
from flint import arb, fmpz, fmpq, ctx
from million_decimal_common import WORK, MIN, record, finish
from math import comb, factorial
from fractions import Fraction
from pathlib import Path
import json
import argparse

def moment_rationals(M,N):
    assert M>=2 and M%2==0
    bases=[fmpz(M-2*j) for j in range(M//2)]
    powers=[2*(-1)**j*fmpz(comb(M,j))*b**M
            for j,b in enumerate(bases)]
    squares=[b*b for b in bases]
    den=fmpz(2)**M*factorial(M)
    for k in range(N+1):
        num=sum(powers,fmpz(0))
        q=fmpq(num,den)
        assert q>0
        yield q
        if k==N: break
        powers=[a*b for a,b in zip(powers,squares)]
        n,d=den*M*M*(2*k+M+1)*(2*k+M+2),(2*k+1)*(2*k+2)
        den,rem=divmod(n,d)
        assert rem==0

def independent_small_moments(M,K):
    cur=[Fraction(1)]+[Fraction(0)]*K
    mu=[Fraction(1,(k+1)*M**k) if k%2==0 else Fraction(0)
        for k in range(K+1)]
    for _ in range(M):
        cur=[sum(comb(k,j)*cur[j]*mu[k-j] for j in range(k+1))
             for k in range(K+1)]
    return cur[::2]

def recurrence(mu, targets, convert):
    # sig[i] = integral P_(k-1)(x) x^(k-1+2i) dmu at step k.
    sig=[convert(q) for q in mu]
    assert sig[0]>0
    prev=None
    beta=None
    result={}
    n=max(targets)
    assert len(sig)==n+1
    for k in range(1,n+1):
        if k==1:
            nxt=sig[1:]
        else:
            nxt=[sig[i+1]-beta*prev[i+1] for i in range(n-k+1)]
        assert nxt[0]>0 and sig[0]>0, ('positive norm',k)
        beta=nxt[0]/sig[0]
        assert beta>0, ('positive recurrence',k)
        if k in targets:
            result[k]=beta/4 # convert X to S_M/M
            print('recurrence',k,'relative bits',getattr(result[k],'rel_accuracy_bits',lambda:None)(),flush=True)
        if k%25==0: print('progress',k,'/',n,flush=True)
        prev,sig=sig,nxt
    return result

def pilot():
    ctx.prec=1024
    M,N=4,12
    q=list(moment_rationals(M,N))
    indie=independent_small_moments(M,2*N)
    assert all(x==fmpq(y.numerator,y.denominator) for x,y in zip(q,indie))
    target=list(range(1,N+1))
    exact=recurrence(q,target,lambda x:x)
    enclosed=recurrence(q,target,arb)
    for n in target:
        assert enclosed[n].contains(arb(exact[n]))
        assert enclosed[n].rel_accuracy_bits()>800
    assert exact[1]==fmpq(1,12*M)
    assert exact[2]==(q[2]/q[1]-q[1])/4
    print('PILOT PASS exact moments, exact recurrence, and Arb overlap at M=4',flush=True)

def full(M):
    assert M in (100,200,400)
    ctx.prec=WORK
    targets=[M//4,M//2,M,2*M,4*M]
    q=list(moment_rationals(M,max(targets)))
    assert q[0]==1 and q[1]==fmpq(1,3*M)
    print('exact moments computed',M,len(q),flush=True)
    values=recurrence(q,targets,arb)
    endpoints={}
    for j,val in values.items():
        assert val.is_finite() and val.rel_accuracy_bits()>=MIN
        record('tab:ul-beta beta_%d^[%d]/M^2'%(j,M),val)
        endpoints[str(j)]={'lower':str(val.lower().fmpq()),'upper':str(val.upper().fmpq())}
    finish('m12-lanczos-'+str(M))
    Path('m12-lanczos-'+str(M)+'.json').write_text(json.dumps({'M':M,'working_bits':WORK,'values':endpoints})+'\n')
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--M',type=int)
    ns=ap.parse_args()
    pilot() if ns.M is None else full(ns.M)
