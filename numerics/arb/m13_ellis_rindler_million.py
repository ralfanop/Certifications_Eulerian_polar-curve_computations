#!/usr/bin/env python3
"""M13 benchmark evaluations of the closed forms in merged PRs #557,
#558 and #568. Parameters below are chosen regression test points, not
asserted to be numerical entries in the manuscript. No integral identity
or Fredholm determinant is certified by evaluating its proposed bound.

Precision: existing million_decimal_common standard (3.6M working bits,
3.4M minimum measured relative bits, 1,000,001 significant digits);
additionally exact nearest-10^-30000 rounding for every positive ball.
"""
import hashlib
import json
from pathlib import Path
from flint import arb, fmpz
from million_decimal_common import WORK, MIN, DIGITS, record, finish

PLACES = 30000
SCALE = fmpz(10) ** PLACES

def fixed_places(name, x):
    assert x.is_finite() and x > 0
    assert x.rel_accuracy_bits() >= MIN
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    assert 0 < lo <= hi
    n = (2*lo.p*SCALE + lo.q)//(2*lo.q)
    assert 2*lo.p*SCALE > (2*n-1)*lo.q, (name, "lower endpoint")
    assert 2*hi.p*SCALE < (2*n+1)*hi.q, (name, "upper endpoint")
    rounded = str(n//SCALE) + "." + str(n%SCALE).zfill(PLACES)
    assert len(rounded.split(".")[1]) == PLACES
    return {"name":name,"decimal_places":PLACES,"relative_bits":x.rel_accuracy_bits(),
            "strict_half_ulp_rounding_cell":True,"rounded_decimal":rounded,
            "rounded_sha256":hashlib.sha256(rounded.encode("ascii")).hexdigest(),
            "lower_endpoint_exact":str(lo),"upper_endpoint_exact":str(hi)}

def fourier(a,q):
    t = a*abs(q)
    return arb.pi()/(2*a)*(1+t)*(-t).exp()

def average(a,p):
    # Closed-form average of the Fourier expression over t in [0,1].
    z = a*abs(p)
    assert z > 0
    return arb.pi()/(2*a)*(2-(z+2)*(-z).exp())/z

def main():
    one = arb(1)
    two = arb(2)
    pi = arb.pi()
    values = [
        ("Ellis closed Fourier a=1,q=1",fourier(one,one)),
        ("Ellis closed Fourier a=1,q=2",fourier(one,two)),
        ("Ellis closed Fourier a=3/2,q=1",fourier(arb(3)/2,one)),
        ("Ellis closed Eulerian average a=1,p=1",average(one,one)),
        ("Ellis closed Eulerian average a=1,p=2",average(one,two)),
        ("Causal kernel energy a=1,kappa=1",pi/4),
        ("Spectral determinant upper bound a=1,kappa=1",(pi/4).exp()),
        ("Rindler sharp essential bound n=1",pi.exp()),
        ("Rindler sharp essential bound n=2",(2*pi).exp()),
    ]
    fixed = []
    for name, ball in values:
        record(name,ball)
        fixed.append(fixed_places(name,ball))
    finish("m13-ellis-rindler")
    Path("m13-ellis-rindler-fixed30000.json").write_text(json.dumps({
        "status":"CERTIFIED","scope":"Selected parameter benchmark closed forms only",
        "source_prs":[557,558,568],"working_bits":WORK,
        "required_relative_bits":MIN,"significant_digits":DIGITS,
        "decimal_places":PLACES,"values":fixed},indent=2),encoding="utf-8")
    print("SUCCESS M13 ELLIS RINDLER STRICT 30000 PLACE GATE",len(fixed),flush=True)

if __name__=="__main__":
    main()
