#!/usr/bin/env python3
"""M12 18 Nov: combine certified profile and Lanczos exact dyadic endpoints.
Run only after verified successful exact-HEAD jobs of PRs #385 and #386.
No claim that supplied endpoints are genuine without those source artifacts."""
from flint import arb, fmpq, ctx
from million_decimal_common import WORK, MIN, exact, record, finish
from fractions import Fraction as Q
from pathlib import Path
import json
import sys

ROWS = [
    ('1/4', '0.010828', '0.010800', '0.010786', '2.70e-5'),
    ('1/2', '0.017171', '0.017111', '0.017081', '4.27e-5'),
    ('1',   '0.017648', '0.017602', '0.017579', '4.39e-5'),
    ('2',   '0.010479', '0.010471', '0.010466', '2.62e-5'),
    ('4',   '0.004340', '0.004341', '0.004342', '1.09e-5'),
]

def load(p):
    return json.loads(p.read_text())

def ball(d):
    lo,hi=fmpq(d['lower']),fmpq(d['upper'])
    assert 0<lo<=hi
    # exact FLINT rationals, dyadic endpoint property
    for q in (lo,hi):
        assert q.q>0 and (int(q.q)&(int(q.q)-1))==0
    x=arb(lo).union(arb(hi))
    assert x.lower().fmpq()<=lo and hi<=x.upper().fmpq()
    assert x.is_finite() and x.rel_accuracy_bits()>=MIN
    return x

def check(name, val, displayed, unit):
    d=Q(displayed)
    assert exact(d-unit/2)<val<exact(d+unit/2), (name,displayed,val.str(16))
    record(name,val)

def main(root):
    assert ctx.prec==WORK
    coeffs={}
    for M in (100,200,400):
        d=load(root/('m12-lanczos-'+str(M)+'.json'))
        assert d['M']==M and d['working_bits']==WORK
        coeffs[M]=d['values']
    for t,*ds in ROWS:
        d=load(root/('m12-profile-'+t.replace('/','-')+'.json'))
        assert d['t']==t and d['working_bits']==WORK and d['relative_bits']>=MIN
        F=ball(d)
        for M,displayed in zip((100,200,400),ds[:3]):
            j=Q(t)*M
            assert j.denominator==1
            c=ball(coeffs[M][str(j.numerator)])
            E=c-F
            assert E>0
            check('tab:ul-beta M*E t='+t+' M='+str(M), M*E,displayed,Q(1,10**6))
            if M==400:
                check('tab:ul-beta E t='+t+' M=400',E,ds[3],Q(1,10**7))
    finish('m12-table-errors')

if __name__=='__main__':
    assert len(sys.argv)==2, 'pass directory with exact-head source JSONs'
    main(Path(sys.argv[1]))
