#!/usr/bin/env python3
"""M12 quartic critical constants, independent Arb certificates.
Source: Manuscript_12_20261125_CROSS_CONNECTIONS, TeX SHA256
67077497bc9095fade4574720628b42ea22fe49f2027d5b075ee9baa45b114d9.
Lean evidence: #624, exact merge a63368ec9bb288ad3647e56ed54ff775d776b748,
CI 45708267481, M12CriticalDCT.F_zero and M12CriticalComplete's two
critical constants. This script certifies rounding, not the analytic limits.
"""
import gzip
import json
import hashlib
from flint import arb, ctx, fmpz
from million_decimal_common import WORK, MIN, DIGITS, record, finish, rounded_significant

assert ctx.prec == WORK == 3600000 and MIN == 3400000 and DIGITS == 1000001
scale = fmpz(10)**DIGITS

def fixed_cell(x):
    assert x.is_finite() and x > 0 and x.rel_accuracy_bits() >= MIN
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    a, b = 2*lo.p*scale, 2*hi.p*scale
    m = (a+lo.q)//(2*lo.q)
    assert a > (2*m-1)*lo.q and b < (2*m+1)*hi.q
    return str(m), str(lo), str(hi)

pi = arb.pi()
g = (arb(1)/4).gamma()
q = arb(40).sqrt().sqrt()
f = q*g/(4*pi.sqrt())
v = 4*pi.sqrt()/(q*g)
c = 2*pi.sqrt()/((pi**2+1)*q*g)
# Additional equivalent expressions must agree at full requested rounding,
# not merely have overlapping intervals. These are algebraic cross-checks,
# not independent evaluations of Gamma itself.
for direct, equivalent in ((v, 1/f), (c, 1/(2*(pi**2+1)*f))):
    assert direct.overlaps(equivalent)
    assert rounded_significant(direct) == rounded_significant(equivalent)
    assert fixed_cell(direct)[0] == fixed_cell(equivalent)[0]
values = [
    ("Fcrit(0) = 40^(1/4) Gamma(1/4)/(4 sqrt(pi))", f),
    ("critical vacuum coefficient = 1/Fcrit(0)", v),
    ("eq:cross-Qzero critical correlation coefficient", c),
]
with gzip.open("m12-quartic-fixed-endpoints.jsonl.gz", "wt", compresslevel=1) as out:
    for name,x in values:
        record(name,x)
        m,lo,hi = fixed_cell(x)
        out.write(json.dumps(dict(name=name, fixed_decimal_places=DIGITS,
            relative_bits=x.rel_accuracy_bits(), rounded_scaled_integer=m,
            rounded_scaled_integer_sha256=hashlib.sha256(m.encode()).hexdigest(),
            lower_exact_dyadic=lo, upper_exact_dyadic=hi))+"\n")
        print(name, "1000001 fixed decimal places: PASS", flush=True)
finish("m12-quartic-constants")
