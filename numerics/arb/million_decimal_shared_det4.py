from million_decimal_common import arb, record, finish
import gzip
import json

# Model in PRs #373 and #376: M(4) = zeta(2) - zeta(3).
# This is the diagonal model, not a physical Maxwell trace certificate.
A = arb.pi()**2 / 6 - arb(3).zeta()
assert A > arb(0)
entries = [
    ("diagonal_fourth_moment", A),
    ("det4_z4_coefficient", -A/4),
    ("det4_fourth_derivative_at_zero", -6*A),
]
with gzip.open("det4-exact-endpoints.jsonl.gz", "wt", encoding="utf-8") as out:
    for name, x in entries:
        record(name, x)
        out.write(json.dumps({"name": name,
            "lower": str(x.lower().fmpq()),
            "upper": str(x.upper().fmpq())}) + "\n")
finish("shared_det4_moment")
