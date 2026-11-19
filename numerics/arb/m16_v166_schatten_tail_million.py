"""Manuscript 16.6 scalar Schatten-four shell asymptotic.
The two representations of the leading constant are independently enclosed.
This does not certify the concrete operator's spectral realization.
"""
import gzip
import json
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish

assert ctx.prec == WORK == 3600000
assert MIN == 3400000 and DIGITS == 1000001
z2 = arb(2).zeta()
z4 = arb(4).zeta()
leading_zeta = z4 / 32
leading_pi = arb.pi()**4 / 2880
assert leading_zeta.overlaps(leading_pi)
values = {
    "tail_leading_zeta4_over_32": leading_zeta,
    "tail_leading_pi4_over_2880": leading_pi,
    "tail_H4_coefficient": 5*z2/16-z4/32,
    "tail_H6_coefficient": -arb(35)/64-5*z2/16,
    "tail_H8_coefficient": arb(35)/64,
}
with gzip.open("m16-v166-tail-endpoints.jsonl.gz", "wt", encoding="utf-8", compresslevel=1) as out:
    for name, x in values.items():
        record(name, x)
        lo, hi = x.lower().fmpq(), x.upper().fmpq()
        out.write(json.dumps({"name": name, "lo_num": str(lo.p), "lo_den": str(lo.q),
                              "hi_num": str(hi.p), "hi_den": str(hi.q)}) + "\n")
finish("m16-v166-tail")
