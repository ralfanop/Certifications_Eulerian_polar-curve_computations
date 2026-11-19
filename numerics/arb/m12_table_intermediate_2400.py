#!/usr/bin/env python3
"""Intermediate Table 1 certification, not a million-decimal certificate.
Only authenticated #427 8192-bit root profiles and #386 full precision
Lanczos endpoint artifacts may be supplied by the pinned workflow.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
from flint import arb,fmpq,fmpz,ctx
import million_decimal_common as common
from m12_table_final_errors import ROWS
from m12_profile_interval_newton import ROWS as PROFILES
P,DIGITS=8192,2400
ctx.prec=P
common.DIGITS=DIGITS
scale=fmpz(10)**DIGITS
root=Path('sources')
def ball(l,u,bits):
    lo,hi=fmpq(l),fmpq(u)
    assert 0<lo<=hi
    for q in (lo,hi):
        assert q.q>0 and (q.q & (q.q-1))==0
    x=arb(lo).union(arb(hi))
    assert x.lower().fmpq()<=lo and hi<=x.upper().fmpq()
    assert x.rel_accuracy_bits()>=bits
    return x
checks=[]
def check(name,x,printed,unit):
    assert x>0 and x.rel_accuracy_bits()>=8000
    d=Q(printed)
    assert common.exact(d-unit/2)<x<common.exact(d+unit/2)
    significant=common.rounded_significant(x)
    lo,hi=x.lower().fmpq(),x.upper().fmpq()
    a,b=2*lo.p*scale,2*hi.p*scale
    m=(a+lo.q)//(2*lo.q)
    assert a>(2*m-1)*lo.q and b<(2*m+1)*hi.q
    checks.append(dict(name=name,printed=printed,relative_bits=x.rel_accuracy_bits(),
        rounded_significant=significant,rounded_scaled_integer=str(m),
        lower=str(lo),upper=str(hi)))
    print('TABLE INTERMEDIATE PASS',name,x.rel_accuracy_bits(),flush=True)
coeffs={}
for M in (100,200,400):
    d=json.loads((root/f'm12-lanczos-{M}.json').read_text())
    assert d['M']==M and d['working_bits']==common.WORK
    assert set(d['values'])=={str(j) for j in (M//4,M//2,M,2*M,4*M)}
    coeffs[M]={j:ball(v['lower'],v['upper'],P-10) for j,v in d['values'].items()}
slugs=dict(zip(('1/4','1/2','1','2','4'),('quarter','half','one','two','four')))
for t,*ds in ROWS:
    d=json.loads((root/f'profile-{slugs[t]}.json').read_text())
    assert d['row']==t and d['working_bits']==P and d['relative_bits']>=P-120
    F=ball(d['F_lower'],d['F_upper'],P-125)
    check('F('+t+')',F,PROFILES[t],Q(1,10**7))
    for M,displayed in zip((100,200,400),ds[:3]):
        j=Q(t)*M
        assert j.denominator==1
        E=coeffs[M][str(j.numerator)]-F
        check('M*E t='+t+' M='+str(M),M*E,displayed,Q(1,10**6))
        if M==400:
            check('E t='+t+' M=400',E,ds[3],Q(1,10**7))
assert len(checks)==25
Path('m12-table-2400.json').write_text(json.dumps(dict(
    source_zip_sha256='7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860',
    working_bits=P,significant_digits=DIGITS,fixed_decimal_places=DIGITS,
    source_runs=[44313014167,44484006385],checks=checks),indent=2)+'\n')
print('TABLE INTERMEDIATE SUCCESS',len(checks),'checks',
      'minimum relative bits',min(x['relative_bits'] for x in checks),flush=True)
