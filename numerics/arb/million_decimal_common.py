"""Strict, exact endpoint decimal rounding and streamed certificates."""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import gzip
import sys
import time
import resource

import flint
from flint import arb, ctx, fmpz, fmpq

WORK, MIN, DIGITS = 3600000, 3400000, 1000001
ctx.prec = WORK
assert flint.__version__ == "0.9.0"
assert ctx.prec == WORK
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
records = []
started = time.monotonic()
rounding_seconds = 0.0
stream = None

def exact(q):
    q = Q(q)
    return arb(q.numerator) / q.denominator

@lru_cache(maxsize=None)
def tenpower(n):
    return fmpz(10)**n if n >= 0 else fmpq(1,fmpz(10)**(-n))

def rounded_significant(x):
    # fmpq exact dyadic endpoints; fmpz large arithmetic avoids Python
    # integer decimal formatting and quadratic long division.
    negative = x < 0
    if negative:
        x = -x
    assert x > 0
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    assert 0 < lo <= hi
    e = 0
    while lo < tenpower(e):
        e -= 1
    while lo >= tenpower(e+1):
        e += 1
    assert hi < tenpower(e+1), "interval spans a decimal decade"
    scale = tenpower(DIGITS-1-e)
    assert isinstance(scale, fmpz)
    a, b = 2*lo.p*scale, 2*hi.p*scale
    m = (a+lo.q)//(2*lo.q)
    assert a > (2*m-1)*lo.q
    assert b < (2*m+1)*hi.q
    if m == tenpower(DIGITS):
        m //= 10
        e += 1
    digits = str(m)
    assert len(digits) == DIGITS
    return ("-" if negative else "")+digits[0]+"."+digits[1:]+"e"+str(e)

def record(name,x):
    global rounding_seconds, stream
    assert x.is_finite() and not x.contains(0), name
    bits = x.rel_accuracy_bits()
    assert bits >= MIN, (name,bits)
    t = time.monotonic()
    rounded = rounded_significant(x)
    ball = x.str(1100000,radius=True,more=True)
    if stream is None:
        stream = gzip.open("million-enclosures.jsonl.gz","wt",compresslevel=1,encoding="utf-8")
    stream.write(json.dumps({"name":name,"relative_bits":bits,"rounded_significant_digits":rounded,"arb_ball":ball})+"\n")
    stream.flush()
    rounding_seconds += time.monotonic()-t
    records.append({"name":name,"relative_bits":bits})
    print(name,"certified relative bits:",bits,"1000001-decimal rounding cell: PASS",flush=True)

def finish(label):
    assert records and stream is not None
    stream.close()
    minimum=min(r["relative_bits"] for r in records)
    elapsed=time.monotonic()-started
    data={"label":label,"python_flint":flint.__version__,"working_bits":WORK,
          "required_relative_bits":MIN,"significant_digits":DIGITS,
          "minimum_relative_bits":minimum,"elapsed_seconds":elapsed,
          "rounding_serialization_seconds":rounding_seconds,
          "peak_rss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          "certificates":records}
    Path("million-"+label+".json").write_text(json.dumps(data,indent=2),encoding="utf-8")
    print("MILLION SUCCESS",label,"checks",len(records),"minimum relative bits",minimum,
          "elapsed seconds",round(time.monotonic()-started,3),
          "peak RSS KiB",resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
