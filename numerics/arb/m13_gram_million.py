#!/usr/bin/env python3
"""Frozen M13, eq:gram, fig:intertwining(b): normalized Gram entries.

For k>=n and k-n even, Rodrigues and n integrations by parts give
M_k(P_n)=k!/((k-n)!! (k+n+1)!!); otherwise it is zero.
For equal parity m,n, start k=max(m,n) and advance by 2. The exact
term ratio is 16(k+1)(k+2)/((k-m+2)(k+m+3)(k-n+2)(k+n+3)).
The remainder is bounded by 55*4**k/k! at the first omitted k,
using |P_n|<=1 and exp(4)<55, as in the historical certificate.
The exact 12 unit diagonal entries and 72 ordered parity zeros are
not numerical relative-accuracy claims. Each row job certifies its
strict upper triangle of equal parity, with symmetry giving the lower.
"""
from fractions import Fraction as Q
from math import factorial, prod
import gzip
import json
import sys


def moment(k, n):
    if k < n or (k-n) % 2:
        return Q(0)
    return Q(factorial(k), prod(range(k-n, 0, -2))*prod(range(k+n+1, 0, -2)))


def ratio(k, m, n):
    return 16*(k+1)*(k+2), (k-m+2)*(k+m+3)*(k-n+2)*(k+n+3)


def regression():
    # Independent Legendre recurrence and exact polynomial integration.
    polys = [[Q(1)], [Q(0), Q(1)]]
    for n in range(1, 11):
        a = [Q(0)] + [Q(2*n+1,n+1)*x for x in polys[n]]
        b = polys[n-1] + [Q(0)]*2
        polys.append([x-Q(n,n+1)*y for x,y in zip(a,b)])
    for n,p in enumerate(polys):
        for k in range(40):
            value = sum(x*Q(1,i+k+1) for i,x in enumerate(p) if (i+k)%2==0)
            assert value == moment(k,n), (k,n)
    for m in range(12):
        for n in range(m,12,2):
            for k in range(n,40,2):
                a = Q(4**k,factorial(k))*moment(k,m)*moment(k,n)
                b = Q(4**(k+2),factorial(k+2))*moment(k+2,m)*moment(k+2,n)
                assert a > 0 and b/a == Q(*ratio(k,m,n))
    assert sum(1 for m in range(12) for n in range(12) if (m+n)%2) == 72
    assert sum(1 for m in range(12) for n in range(m+2,12,2)) == 30
    print('EXACT MOMENT AND RATIO REGRESSION PASS', flush=True)


def main(m):
    from flint import fmpz
    from million_decimal_common import arb, ctx, WORK, MIN, exact, record, finish
    assert ctx.prec == WORK and arb(4).exp() < 55
    K = 125000

    def split(a,b,k0,i,j):
        # T/Q sums products of the successive ratios, beginning with 1.
        if b-a == 1:
            p,q = ratio(k0+2*a,i,j)
            return fmpz(p),fmpz(q),fmpz(q)
        mid=(a+b)//2
        p1,q1,t1=split(a,mid,k0,i,j)
        p2,q2,t2=split(mid,b,k0,i,j)
        return p1*p2,q1*q2,t1*q2+p1*t2

    def raw(i,j):
        k0=max(i,j)
        assert (i+j)%2==0
        first=Q(4**k0,factorial(k0))*moment(k0,i)*moment(k0,j)
        assert first>0
        _,q,t=split(0,K,k0,i,j)
        omitted=k0+2*K
        tail=arb(55)*(arb(4)**omitted)/arb(factorial(omitted))
        assert tail < arb(2)**(-3500000)
        v=exact(first)*arb(t)/arb(q)+arb(0,tail.upper())
        assert v>0 and v.rel_accuracy_bits()>=MIN, (i,j,v.rel_accuracy_bits())
        return v

    assert 0<=m<10
    diagonal=raw(m,m)
    prev=arb(1)
    label=f'm13-gram-row-{m}'
    with gzip.open(label+'-endpoints.jsonl.gz','wt',encoding='utf-8',compresslevel=1) as f:
        for n in range(m+2,12,2):
            val=raw(m,n)/(diagonal*raw(n,n)).sqrt()
            assert 0<val<prev, (m,n,'positivity, strict row decrease')
            prev=val
            # The maximum is separated from every competitor by this rational.
            if (m,n)==(0,2):
                assert exact(Q('0.75317'))<val<exact(Q('0.753175'))
                assert exact(Q('0.7531740399525'))<val<exact(Q('0.7531740399535'))
            else:
                assert val<exact(Q('0.75317')), (m,n,'maximum separation')
            name=f'fig:intertwining(b) g_{m}_{n}'
            record(name,val)
            lo,hi=val.lower().fmpq(),val.upper().fmpq()
            f.write(json.dumps({'m':m,'n':n,'relative_bits':val.rel_accuracy_bits(),
                'lo_num':str(lo.p),'lo_den':str(lo.q),
                'hi_num':str(hi.p),'hi_den':str(hi.q)})+'\n')
    finish(label)


if __name__=='__main__':
    regression()
    if len(sys.argv)>1 and sys.argv[1] != 'regression':
        main(int(sys.argv[1]))
