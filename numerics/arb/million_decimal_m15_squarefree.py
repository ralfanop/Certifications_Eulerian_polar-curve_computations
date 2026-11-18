from million_decimal_common import arb, record, finish
import gzip, json

# Standard squarefree diagonal subcase of PR #372, s=2:
# zeta(2k)/zeta(4k), k=1,2,3. These are analytic benchmark quantities,
# not a certificate of the geometric operator or of an Euler-product identity.
pi = arb.pi()
entries = [
    ("squarefree_moment_s2_k1", arb(2).zeta() / arb(4).zeta(), 15/pi**2),
    ("squarefree_moment_s2_k2", arb(4).zeta() / arb(8).zeta(), 105/pi**4),
    ("squarefree_moment_s2_k3", arb(6).zeta() / arb(12).zeta(), arb(675675)/(691*pi**6)),
]
with gzip.open("squarefree-exact-endpoints.jsonl.gz", "wt", encoding="utf-8") as out:
    for name, x, y in entries:
        assert x > 0 and x.overlaps(y)
        record(name, x)
        out.write(json.dumps({"name": name, "lower": str(x.lower().fmpq()),
            "upper": str(x.upper().fmpq())}) + "\n")
finish("m15_squarefree_moments")
