"""Shared exact-decimal rounding certificate for the 100000-digit pilot."""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import sys
import time
import resource

import flint
from flint import arb, ctx

WORK, MIN, DIGITS = 360000, 340000, 100000
ctx.prec = WORK
assert flint.__version__ == "0.9.0"
assert ctx.prec == WORK
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
records = []
started = time.monotonic()
rounding_seconds = 0.0

def exact(q):
    q = Q(q)
    return arb(q.numerator) / q.denominator

def endpoint(x):
    q = x.fmpq()
    return Q(int(q.p), int(q.q))

@lru_cache(maxsize=None)
def tenpower(n):
    return 10**n if n >= 0 else Q(1,10**(-n))

def rounded_significant(x):
    # Work with exact dyadic endpoints, not with a rounded display string.
    negative = x < 0
    if negative:
        x = -x
    assert x > 0
    lo, hi = endpoint(x.lower()), endpoint(x.upper())
    assert 0 < lo <= hi
    e = 0
    while lo < tenpower(e):
        e -= 1
    while lo >= tenpower(e+1):
        e += 1
    assert hi < tenpower(e+1), "interval spans a decimal decade"
    scale = tenpower(DIGITS-1-e)
    assert isinstance(scale, int)
    # Rounded candidate from exact lower endpoint; both endpoints must be
    # STRICTLY inside the same nearest rounding cell (no tie ambiguity).
    m = (2*lo.numerator*scale+lo.denominator)//(2*lo.denominator)
    assert 2*lo.numerator*scale > (2*m-1)*lo.denominator
    assert 2*hi.numerator*scale < (2*m+1)*hi.denominator
    if m == tenpower(DIGITS):
        m //= 10
        e += 1
    digits = str(m)
    assert len(digits) == DIGITS
    return ("-" if negative else "") + digits[0]+"."+digits[1:]+"e"+str(e)

def record(name,x):
    global rounding_seconds
    assert x.is_finite() and not x.contains(0), name
    bits = x.rel_accuracy_bits()
    assert bits >= MIN, (name,bits)
    t = time.monotonic()
    rounded = rounded_significant(x)
    ball = x.str(110000,radius=True,more=True)
    rounding_seconds += time.monotonic()-t
    records.append({"name":name,"relative_bits":bits,"rounded_significant_digits":rounded,"arb_ball":ball})
    print(name,"certified relative bits:",bits,"100000-decimal rounding cell: PASS",flush=True)

def finish(label):
    assert records
    minimum=min(r["relative_bits"] for r in records)
    elapsed=time.monotonic()-started
    data={"label":label,"python_flint":flint.__version__,"working_bits":WORK,
          "required_relative_bits":MIN,"significant_digits":DIGITS,
          "minimum_relative_bits":minimum,"elapsed_before_json_seconds":elapsed,
          "rounding_serialization_seconds":rounding_seconds,
          "peak_rss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          "certificates":records}
    Path("pilot-"+label+".json").write_text(json.dumps(data,indent=2),encoding="utf-8")
    print("PILOT SUCCESS",label,"checks",len(records),"minimum relative bits",minimum,
          "elapsed seconds",round(time.monotonic()-started,3),
          "peak RSS KiB",resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
