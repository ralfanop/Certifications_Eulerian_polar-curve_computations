#!/usr/bin/env python3
"""M12 exact fixed-place replay without recomputing the costly Lanczos moments.

Two independent exact rounding tests: 1,000,001 significant digits and
1,000,001 fixed decimal places. Reuse the published #386 dyadic endpoints
only after the workflow verifies the artifact identity and digest.
No new interval counts are asserted for already certified quantities.
The errors mode is a prepared consumer, NOT a Table 1 full certificate;
run it only on authenticated successful full-precision source artifacts.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

from flint import arb, fmpq, fmpz, ctx
import million_decimal_common as common

WORK, MIN, DIGITS = common.WORK, common.MIN, common.DIGITS
assert ctx.prec == WORK == 3600000 and DIGITS == 1000001
SCALE=fmpz(10)**DIGITS
checks=[]
stream=None

def record(name,x):
    assert ctx.prec==WORK
    assert x.is_finite() and not x.contains(0)
    bits=x.rel_accuracy_bits()
    assert bits>=MIN, (name,bits)
    significant=common.rounded_significant(x)
    lo,hi=x.lower().fmpq(),x.upper().fmpq()
    a,b=2*lo.p*SCALE,2*hi.p*SCALE
    m=(a+lo.q)//(2*lo.q)
    assert a>(2*m-1)*lo.q and b<(2*m+1)*hi.q, name
    value=str(m)
    stream.write(json.dumps(dict(name=name,relative_bits=bits,
        fixed_decimal_places=DIGITS, rounded_scaled_integer=value,
        rounded_scaled_integer_sha256=hashlib.sha256(value.encode()).hexdigest(),
        rounded_significant_digits=significant,
        lower_exact_dyadic=str(lo),upper_exact_dyadic=str(hi)))+'\n')
    stream.flush()
    checks.append(dict(name=name,relative_bits=bits))
    print('FIXED AND SIGNIFICANT PASS',name,bits,flush=True)

def finish(label):
    assert checks
    print('FIXED REPLAY SUCCESS',label,'checks',len(checks),
          'minimum relative bits',min(x['relative_bits'] for x in checks),flush=True)

def lanczos(root):
    for M in (100,200,400):
        d=json.loads((root/f'm12-lanczos-{M}.json').read_text())
        assert d['M']==M and d['working_bits']==WORK
        assert set(d['values'])=={str(j) for j in (M//4,M//2,M,2*M,4*M)}
        for j,v in d['values'].items():
            lo,hi=fmpq(v['lower']),fmpq(v['upper'])
            assert 0<lo<=hi
            for q in (lo,hi):
                assert q.q>0 and (q.q & (q.q-1))==0
            x=arb(lo).union(arb(hi))
            assert x.lower().fmpq()<=lo and hi<=x.upper().fmpq()
            record(f'tab:ul-beta beta_{j}^[{M}]/M^2',x)
    finish('m12-lanczos')

def main():
    global stream
    ap=argparse.ArgumentParser()
    ap.add_argument('mode',choices=('historical','additional','lanczos','errors'))
    ap.add_argument('--root',type=Path,default=Path('sources'))
    ns=ap.parse_args()
    target={'historical':8,'additional':20,'lanczos':15,'errors':20}[ns.mode]
    common.record=record
    common.finish=finish
    with gzip.open('m12-fixed-'+ns.mode+'.jsonl.gz','wt',compresslevel=1) as out:
        stream=out
        if ns.mode=='historical':
            from million_decimal_m11_13 import m12
            m12()
            finish('m12')
        elif ns.mode=='additional':
            import m12_final_scalar_million
        elif ns.mode=='lanczos':
            lanczos(ns.root)
        else:
            from m12_table_final_errors import main as errors
            errors(ns.root)
    assert len(checks)==target
    Path('m12-fixed-'+ns.mode+'.json').write_text(json.dumps({
        'source_zip_sha256':'7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860',
        'mode':ns.mode,'working_bits':WORK,'significant_digits':DIGITS,
        'fixed_decimal_places':DIGITS,'checks':checks},indent=2)+'\n')

if __name__=='__main__':
    main()
