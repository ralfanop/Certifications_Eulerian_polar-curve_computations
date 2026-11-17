"""M16 v16.5 §14.1: chosen scalar benchmark inputs, not an operator certificate."""
import gzip
import json
import subprocess
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish

ctx.prec = 3600000
assert (ctx.prec, WORK, MIN, DIGITS) == (3600000, 3600000, 3400000, 1000001)
head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
label = "m16-v165-evanescent"
# Below-threshold: |kappa|²=3, k²=1. Above-threshold: reverse them.
# Both alpha and p are sqrt(2), distance r=0 or r=1.
alpha = arb(2).sqrt()
p = arb(2).sqrt()
values = {
    "alpha_gap2": alpha,
    "G_gap2_r0": 1 / (2 * alpha),
    "G_gap2_r1": (-alpha).exp() / (2 * alpha),
    "outgoing_density_gap2_r0": 1 / (2 * arb.pi() * p),
    "outgoing_density_gap2_r1": p.cos() / (2 * arb.pi() * p),
}
with gzip.open(label + "-endpoints.jsonl.gz", "wt", encoding="utf-8", compresslevel=1) as out:
    for name, x in values.items():
        assert ctx.prec == 3600000
        assert x.is_finite() and not x.contains(0), name
        assert x.rel_accuracy_bits() >= 3400000, (name, x.rel_accuracy_bits())
        # Common helper asserts strict exact endpoint rounding-cell containment
        # and persists the rounding and rigorous ball in a streamed artifact.
        record(name, x)
        lo, hi = x.lower().fmpq(), x.upper().fmpq()
        out.write(json.dumps({"name":name, "head":head,
            "lower":[str(lo.p),str(lo.q)], "upper":[str(hi.p),str(hi.q)],
            "relative_bits":x.rel_accuracy_bits()}) + "\n")
finish(label)
# The below-threshold formula is real: its imaginary part is exactly zero.
# No relative precision or rounded significant digits are attributed to zero.
with open(label + "-exact.json", "w", encoding="utf-8") as out:
    json.dump({"head":head, "source_zip_sha256":
        "4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e",
        "exact_zero":"Im of explicitly real below-threshold scalar formula at r=0,1",
        "exact_rational":"gap squared 2, r=0 or 1; multiplier at t=0 is 1/2",
        "scope":"formula evaluation only; no spectral/kernel identification"}, out, indent=2)
