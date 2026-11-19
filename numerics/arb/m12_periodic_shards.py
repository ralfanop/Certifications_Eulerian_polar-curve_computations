#!/usr/bin/env python3
"""Certified sharding of the merged #418 periodic H(S) integration.

Each shard encloses a disjoint contiguous set of interior quadrant
nodes. The finalizer checks exact coverage, adds the two endpoint
terms, divides by the total number of full period nodes, and adds
the analytically certified strip tail exactly ONCE. This is an
8192-bit sharding pilot, plus full-working-precision NODE timing
only. Neither test certifies a million-digit integral or profile.
"""
import argparse
import json
from pathlib import Path
import time
from flint import arb, fmpq, ctx
from million_decimal_common import WORK, MIN
from m12_profile_periodic_strip import strip_bound, periodic

def plan(S,bits):
    ctx.prec=bits
    a=arb(1)/2
    while S*a>3:
        a/=2
    for _ in range(15):
        M,boxes=strip_bound(S,a)
        if M is not None:
            break
        a/=2
    assert M is not None
    goal=bits-48 if bits<WORK else MIN+64
    k=int((arb(goal+32)*arb(2).log()/a).ceil().unique_fmpz())
    N=4*((k+3)//4)
    tail=S*S*M/(a*N).expm1()
    while not tail<arb(2)**(-goal):
        N+=4
        tail=S*S*M/(a*N).expm1()
    print('SHARD PLAN',S.str(10),'bits',bits,'N',N,'boxes',boxes,
          'strip',a.str(10),flush=True)
    return N,tail

def node(S,aS,step,j):
    theta=j*step
    s=S*theta.sin()
    c=theta.cos()
    assert s>0 and c>0
    v=arb(1)/2+1/s.expm1()-1/s
    rad=aS*aS-v*v
    assert rad>0
    return 4*c*rad.sqrt()/S

def bounds(m,i,K):
    return 1+(m-1)*i//K,1+(m-1)*(i+1)//K

def worker(s,bits,i,K):
    S=arb(s)
    N,_=plan(S,bits)
    m=N//4
    lo,hi=bounds(m,i,K)
    aS=arb(1)/2+1/S.expm1()-1/S
    step=arb.pi()/(2*m)
    t=time.monotonic()
    total=arb(0)
    for j in range(lo,hi):
        total+=node(S,aS,step,j)
    assert total.is_finite() and total>0
    assert total.rel_accuracy_bits()>=bits-100
    out=dict(S=s,bits=bits,N=N,index=i,shards=K,lo=lo,hi=hi,
             lower=str(total.lower().fmpq()),upper=str(total.upper().fmpq()))
    Path(f'm12-shard-{s}-{i}.json').write_text(json.dumps(out)+'\n')
    print('SHARD SUCCESS',s,i,'nodes',hi-lo,'relative bits',total.rel_accuracy_bits(),
          'seconds',time.monotonic()-t,flush=True)

def combine(s,bits,K,root):
    S=arb(s)
    N,tail=plan(S,bits)
    m=N//4
    aS=arb(1)/2+1/S.expm1()-1/S
    # Periodic sum: endpoint at 0 twice; endpoint pi/2 is exactly 0.
    total=2*aS/S
    end=1
    for i in range(K):
        d=json.loads((root/f'm12-shard-{s}-{i}.json').read_text())
        lo,hi=bounds(m,i,K)
        assert (d['S'],d['bits'],d['N'],d['index'],d['shards'],d['lo'],d['hi'])==(s,bits,N,i,K,lo,hi)
        assert lo==end and hi>lo
        end=hi
        l,u=fmpq(d['lower']),fmpq(d['upper'])
        for q in (l,u):
            assert q.q>0 and (q.q & (q.q-1))==0
        assert 0<l<=u
        x=arb(l).union(arb(u))
        assert x.lower().fmpq()<=l and u<=x.upper().fmpq()
        assert x.rel_accuracy_bits()>=bits-100
        total+=x
    assert end==m
    H=S*S*total/(2*N)+arb(0,tail.upper())
    assert H.rel_accuracy_bits()>=bits-100 and H>0
    # Independently evaluate the complete, merged #418 rule.
    ref=periodic(S,bits-48)
    assert H.overlaps(ref)
    Path(f'm12-sharded-{s}.json').write_text(json.dumps(dict(
        S=s,bits=bits,relative_bits=H.rel_accuracy_bits(),
        lower=str(H.lower().fmpq()),upper=str(H.upper().fmpq()),
        N=N,shards=K,scope='8192-bit sharding pilot only'))+'\n')
    print('SHARDED QUADRATURE SUCCESS',s,'bits',bits,'relative bits',
          H.rel_accuracy_bits(),'shards',K,flush=True)

def sample(s):
    S=arb(s)
    N,_=plan(S,WORK)
    m=N//4
    aS=arb(1)/2+1/S.expm1()-1/S
    step=arb.pi()/(2*m)
    timings=[]
    for j in (1,m//8,m//4,m//2,3*m//4,7*m//8,m-1):
        start=time.monotonic()
        x=node(S,aS,step,j)
        elapsed=time.monotonic()-start
        assert x.is_finite() and x>0 and x.rel_accuracy_bits()>=MIN
        timings.append(elapsed)
        print('FULL WORK NODE SAMPLE',s,j,'bits',x.rel_accuracy_bits(),
              'seconds',elapsed,flush=True)
    print('NODE TIMING SUCCESS',s,'N',N,'interior nodes',m-1,
          'sample max seconds',max(timings),
          'NOT a full quadrature',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('mode',choices=['worker','combine','sample'])
    ap.add_argument('S',type=int,choices=[4,93])
    ap.add_argument('--bits',type=int,default=8192)
    ap.add_argument('--index',type=int,default=0)
    ap.add_argument('--shards',type=int,default=4)
    ap.add_argument('--root',type=Path,default=Path('.'))
    ns=ap.parse_args()
    assert ns.bits==8192 and ns.shards==4
    if ns.mode=='worker':
        assert 0<=ns.index<ns.shards
        worker(ns.S,ns.bits,ns.index,ns.shards)
    elif ns.mode=='combine':
        combine(ns.S,ns.bits,ns.shards,ns.root)
    else:
        sample(ns.S)
