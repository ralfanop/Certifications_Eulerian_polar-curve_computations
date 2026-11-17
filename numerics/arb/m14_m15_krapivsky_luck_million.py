#!/usr/bin/env python3
"""M14 det-mobius / M15 §6.6: explicit special-function scalar values.
This evaluates the written sine-integral expressions, not the unresolved
Binet equality or an analytic continuation of a prime sum.
"""
import gzip
import json
from pathlib import Path
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish

assert (WORK, MIN, DIGITS, ctx.prec) == (3600000, 3400000, 1000001, 3600000)
pi = arb.pi()
si = (2*pi).si()
c = si/pi
s = arb(1)/2-c
assert c > 0 and s > 0
with gzip.open("kl-endpoints.jsonl.gz", "wt", encoding="utf-8", compresslevel=1) as out:
    for name, x in [
        ("Si(2*pi)", si),
        ("Si(2*pi)/pi", c),
        ("1/2-Si(2*pi)/pi", s),
        ("2*Si(2*pi) (linear integral expression)", 2*si),
        ("4*Si(2*pi) (central squared-profile energy expression)", 4*si),
        ("4*pi*(1/2-Si(2*pi)/pi) (tail energy expression)", 4*pi*s),
        ("2/(4*pi^2) (kernel majorant coefficient)", 2/(4*pi*pi)),
    ]:
        assert x.rel_accuracy_bits() >= MIN
        record(name,x)
        l,h=x.lower().fmpq(),x.upper().fmpq()
        out.write(json.dumps({"name":name,"lower":[str(l.p),str(l.q)],
            "upper":[str(h.p),str(h.q)]})+"\n")
Path("kl-exact.json").write_text(json.dumps({
    "M15_source_zip_sha256":"d44a7ac1d0d9501bc7d9aed5d345afb1dcd11a18c0d4ec540806e9c16bc1980c",
    "exact_rational_sum":"1/2",
    "proof_of_scalar_identity":"C=Si(2*pi)/pi and S=1/2-C imply C+S=1/2 by definition; this is not a proof of the integral identity."
},indent=2),encoding="utf-8")
finish("kl-sine-integral")
