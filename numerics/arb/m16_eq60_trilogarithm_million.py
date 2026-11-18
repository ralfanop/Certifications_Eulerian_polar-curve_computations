"""M16.6 equation (60): strict million-significant-digit certificates.

The integral and series are evaluated through the exact analytic identity
in Eq60Trilogarithm.lean, not by numerical quadrature or truncation.
The second route replaces zeta(2) by pi^2/6.
"""
import gzip
import json
from flint import arb
from million_decimal_common import WORK, MIN, DIGITS, record, finish

z2 = arb(2).zeta()
z3 = arb(3).zeta()
a = z2 - z3
b = arb.pi()**2 / 6 - z3
c = 1 + z3 - z2
d = 1 + z3 - arb.pi()**2 / 6
assert a.overlaps(b)
assert c.overlaps(d)
assert a.overlaps(1-c)
assert b.overlaps(1-d)

values = {
    "zeta_difference": a,
    "zeta_difference_pi_route": b,
    "integral_series_complement": c,
    "integral_series_complement_pi_route": d,
}
with gzip.open("m16-eq60-endpoints.jsonl.gz", "wt", compresslevel=1) as out:
    for name, x in values.items():
        record(name, x)
        lo, hi = x.lower().fmpq(), x.upper().fmpq()
        out.write(json.dumps({
            "name": name, "lower": [str(lo.p), str(lo.q)],
            "upper": [str(hi.p), str(hi.q)]
        }) + "\n")
finish("m16-eq60-trilogarithm")
