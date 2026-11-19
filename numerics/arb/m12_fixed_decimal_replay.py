#!/usr/bin/env python3
"""Replay M12 existing verified enclosures, testing *fixed* decimals.

For scalars, the source's arb_ball is the decimal ball emitted with
radius=True by arb.str, not the rounded significant-digit midpoint.
FLINT's decimal ball printing contract encloses the original binary ball:
https://flintlib.org/doc/arb/printing.html
Reparse outward at WORK precision; recheck the old significant rounding
against the archived string and independently test the new fixed cell.
For finite Lanczos, use exact dyadic endpoint JSON from the original job
and additionally check consistent significant rounding.
Source ZIP identity, exact HEAD and successful run checked by CI.
No new mathematical evaluations or profile certificates.
"""
import argparse
import gzip
import hashlib
import json
import re
import zipfile
from pathlib import Path
from flint import arb, ctx, fmpq, fmpz
from million_decimal_common import WORK, MIN, DIGITS, rounded_significant

def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()

def interval(item):
    lo,hi=fmpq(item['lower']),fmpq(item['upper'])
    assert 0 < lo <= hi
    for q in (lo,hi):
        d=int(q.q)
        assert d>0 and not (d&(d-1))
    x=arb(lo).union(arb(hi))
    assert x.lower().fmpq()<=lo and hi<=x.upper().fmpq()
    return x

def fixed_cell(x,scale):
    lo,hi=x.lower().fmpq(),x.upper().fmpq()
    assert lo<=hi
    a,b=2*lo.p*scale,2*hi.p*scale
    m=(a+lo.q)//(2*lo.q)
    assert a>(2*m-1)*lo.q and b<(2*m+1)*hi.q
    return str(m),lo,hi

def main(path,label,expected,artifact_id):
    assert ctx.prec==WORK==3600000 and DIGITS==1000001
    scale=fmpz(10)**DIGITS
    seen=set()
    minimum=WORK
    with zipfile.ZipFile(path) as z:
        # Require one exact name; no archive extraction or path traversal.
        assert z.namelist().count('million-enclosures.jsonl.gz')==1
        lanczos=None
        if label.startswith('lanczos-'):
            M=int(label.split('-')[1])
            source=json.loads(z.read(f'm12-lanczos-{M}.json'))
            assert source['M']==M and source['working_bits']==WORK
            lanczos=source['values']
            assert set(lanczos)=={str(j) for j in (M//4,M//2,M,2*M,4*M)}
        with z.open('million-enclosures.jsonl.gz') as raw, gzip.open(raw,'rt',encoding='utf-8') as rows, gzip.open(f'm12-fixed-{label}.jsonl.gz','wt',encoding='utf-8',compresslevel=1) as out:
            for line in rows:
                d=json.loads(line)
                name=d['name']
                assert name not in seen and d['relative_bits']>=MIN
                seen.add(name)
                if lanczos is None:
                    # Guaranteed containing decimal ball; require explicit radius.
                    assert '+/-' in d['arb_ball']
                    x=arb(d['arb_ball'])
                else:
                    match=re.fullmatch(r'tab:ul-beta beta_(\d+)\^\[(\d+)\]/M\^2',name)
                    assert match and int(match[2])==M,(name,M)
                    x=interval(lanczos[match[1]])
                assert x.is_finite() and not x.contains(0)
                acc=x.rel_accuracy_bits()
                assert acc>=MIN,(name,acc)
                assert rounded_significant(x)==d['rounded_significant_digits'],name
                m,lo,hi=fixed_cell(x,scale)
                out.write(json.dumps(dict(name=name,source_artifact=artifact_id,
                     source_ball_sha256=digest(d['arb_ball']),
                     significant_digits_sha256=digest(d['rounded_significant_digits']),
                     relative_bits=acc,fixed_decimal_places=DIGITS,
                     rounded_scaled_integer=m,rounded_scaled_integer_sha256=digest(m),
                     lower_exact_dyadic=str(lo),upper_exact_dyadic=str(hi)))+'\n')
                minimum=min(minimum,acc)
                print('FIXED DECIMAL PASS',label,name,'relative bits',acc,flush=True)
    assert len(seen)==expected
    print('FIXED REPLAY SUCCESS',label,'checks',len(seen),'minimum relative bits',minimum,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('archive',type=Path)
    p.add_argument('label')
    p.add_argument('expected',type=int)
    p.add_argument('artifact_id',type=int)
    a=p.parse_args()
    main(a.archive,a.label,a.expected,a.artifact_id)
