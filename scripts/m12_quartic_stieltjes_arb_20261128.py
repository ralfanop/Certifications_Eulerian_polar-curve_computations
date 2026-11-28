#!/usr/bin/env python3
"""Rigorous FLINT/Arb decimal truncation of M12 §9.13 closed forms.
No assertion that the independent analytic identities are numerically proved.
Two equivalent Gamma routes are checked, including Gamma(3/4).
"""
import hashlib, json, pathlib, sys
from flint import arb, fmpz, fmpq, ctx
sys.set_int_max_str_digits(0)
BITS = 3600000
DIGITS = 1000001
ctx.prec = BITS
out = pathlib.Path("m12-stieltjes-arb")
out.mkdir(exist_ok=True)
p = arb.pi()
g = arb.const_euler()
q = arb(fmpq(1,4)).gamma()
r = arb(fmpq(3,4)).gamma()
F = arb(40).sqrt().sqrt()*q/(4*p.sqrt())
A = q*q/(32*p).sqrt()
A2 = q*p.sqrt()/(4*r)
logQ = (5*p/(8*F**4)).log()
logQ2 = (p*p/(8*A2*A2)).log()
d = -p*(g+(5*p/(2*F**4)).log())
d2 = -p*(g+4*arb(2).log()+3*p.log()-4*q.log())
ld = g+logQ
ld2 = -arb(4).log()-d2/p
M = p/2*logQ
M2 = p/2*logQ2
scale = arb(fmpz(10)**DIGITS)
records = {}
def prefix(x):
    if x > 0:
        sign, y = "", x
    elif x < 0:
        sign, y = "-", -x
    else:
        raise ArithmeticError("ambiguous sign")
    # A single integer for the floor of the entire scaled ball is mandatory.
    z = (y*scale).floor().unique_fmpz()
    if z is None:
        raise ArithmeticError("decimal prefix not determined at requested precision")
    raw = str(z).zfill(DIGITS+1)
    return sign+raw[:-DIGITS]+"."+raw[-DIGITS:]
def record(name,x,y):
    assert x.overlaps(y), name
    a,b = prefix(x),prefix(y)
    assert a == b, name
    data = (a+"\n").encode("ascii")
    (out/(name+".txt")).write_bytes(data)
    records[name] = {"fractional_digits":DIGITS,"sha256":hashlib.sha256(data).hexdigest(),
                     "preview":a[:72], "two_gamma_routes":True}
    print(name, a[:72], flush=True)
record("Fcrit0",F,(A2/(p/5).sqrt()).sqrt())
record("lemniscate_A",A,A2)
record("stieltjes_quarter_difference",d,d2)
record("beta_logarithmic_derivative",ld,ld2)
record("normalized_logarithmic_Mellin_moment",logQ,logQ2)
record("logarithmic_Mellin_integral",M,M2)
record("beta_derivative",p/4*ld,p/4*ld2)
(out/"manifest.json").write_text(json.dumps({"working_bits":BITS,"fractional_digits":DIGITS,
  "rounding":"toward zero; identical floor of positive scaled interval",
  "scope":"closed forms only; two overlapping enclosures do not independently prove Connon or Mellin identities",
  "records":records},indent=2)+"\n")
print("SUCCESS: 7 scalar closed forms, 1000001 exact fractional digits each")
