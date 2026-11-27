#!/usr/bin/env python3
"""M16 section 9.5, eqs. (168), (172), unperturbed threshold.
Source TeX SHA256 6c65e431dbf8801a0e776525fb8d1c67c33a66f8356566891635b8bbb3f50f35.
Numerical enclosures only, not proofs of operator statements.
"""
import gzip, json, hashlib
from flint import arb, ctx, fmpz
from million_decimal_common import WORK, MIN, DIGITS, rounded_significant, record, finish

assert ctx.prec == WORK == 3600000 and MIN == 3400000 and DIGITS == 1000001
scale = fmpz(10)**DIGITS

def fixed(x):
    assert x.is_finite() and x > 0 and x.rel_accuracy_bits() >= MIN
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    a, b = 2*lo.p*scale, 2*hi.p*scale
    m = (a+lo.q)//(2*lo.q)
    assert a > (2*m-1)*lo.q and b < (2*m+1)*hi.q
    return str(m),str(lo),str(hi)

s = arb(2).sqrt()
q = 1/s
threshold = arb(3).sqrt()
assert (s*s).contains(arb(2))
assert (q*s).contains(arb(1))
assert (2*threshold*threshold).contains(arb(6))
vals = [
    ("eq:krein-normalized-block sqrt(2)",s),
    ("eq:krein-normalized-block 1/sqrt(2)",q),
    ("cor:krein-block-gap unperturbed threshold sqrt(3)",threshold),
]
with gzip.open("m16-krein-fixed-endpoints.jsonl.gz","wt",compresslevel=1) as out:
    for name,x in vals:
        record(name,x)
        m,lo,hi=fixed(x)
        out.write(json.dumps(dict(name=name, fixed_decimal_places=DIGITS,
          relative_bits=x.rel_accuracy_bits(),rounded_scaled_integer=m,
          rounded_scaled_integer_sha256=hashlib.sha256(m.encode()).hexdigest(),
          lower_exact_dyadic=lo,upper_exact_dyadic=hi))+"\n")
        print(name,"1000001 fixed decimal places: PASS",flush=True)
finish("m16-krein-spatial")
