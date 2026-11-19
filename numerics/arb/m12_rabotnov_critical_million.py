"""Additional M12 scalar checks against authoritative archive 7ae7cd218...8860.
These verify scalar values, not analytic identities, disk convexity or limits.
Both significant digits and fixed decimal places are tested separately.
"""
from flint import arb, ctx, fmpz
from million_decimal_common import WORK, MIN, DIGITS, record, finish
import gzip
import json
import hashlib

assert ctx.prec == WORK == 3600000 and DIGITS == 1000001
scale = fmpz(10)**DIGITS

def fixed_cell(x):
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    assert lo <= hi
    a, b = 2*lo.p*scale, 2*hi.p*scale
    m = (a+lo.q)//(2*lo.q)
    assert a > (2*m-1)*lo.q and b < (2*m+1)*hi.q
    return str(m), lo, hi

pi = arb.pi()
s = (pi/2).sinh()
d = pi**2+1
values = [
    ("eq:rabotnov-pi (174) F_E(pi^2)", 2*pi*s),
    ("eq:rabotnov-negpi (175) F_E(-pi^2)", -2*pi),
    ("eq:rabotnov-ratio (176) sinh(pi/2)", s),
    ("eq:rabotnov-ratio (176) r_E(i pi)", 2*s/pi),
    ("eq:rabotnov-eulerian (173) pi^2 specialization parameter", pi**2),
    ("eg:eq:15proved (273) critical coefficient in c-1/12", arb(6).sqrt()/d),
    ("eg:eq:restored-36 (274) vacuum limit", arb(24).sqrt()),
    ("eg:eq:restored-37 (275) Q slope", 1/(2*d)),
    ("eg:eq:lambda-min (264) alternate phase candidate", 2*pi**2/(3*d)),
]
assert values[-1][1] > 2/d
with gzip.open("m12-fixed-decimal-endpoints.jsonl.gz", "wt", compresslevel=1) as out:
    for name,x in values:
        record(name,x)
        m,lo,hi = fixed_cell(x)
        out.write(json.dumps({"name":name,"fixed_decimal_places":DIGITS,
            "rounded_scaled_integer":m,"rounded_scaled_integer_sha256":hashlib.sha256(m.encode()).hexdigest(),
            "lower_exact_dyadic":str(lo),"upper_exact_dyadic":str(hi)})+"\n")
        print(name,"1000001 fixed decimal places: PASS",flush=True)
finish("m12-rabotnov-critical")
