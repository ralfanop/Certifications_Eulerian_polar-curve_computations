#!/usr/bin/env python3
"""M13 25 Nov cross-throatself: rigorous numerical certificate.
Frozen ZIP 283b38ea4d3ed2380ff7018ba9cdd6d1c5625246d8eb9713970cbd6ad810b8e8.
13/13.tex SHA256 4febb370e6329cae2c94e88f4171e652bdeed6616b976fa728f83259e7b275f9.
Two independent enclosed expressions:
T(1/sqrt(2)) = K(1/sqrt(2))/sqrt(2), using the classical AGM formula,
and sqrt(pi/5)*Fcrit(0)^2 using the M12 critical Gamma expression.
The AGM limit is bracketed by finite geometric/arithmetic iterates.
The numerical agreement does not prove the analytic identities.
"""
import json
import hashlib
from pathlib import Path
from flint import arb, fmpz
from million_decimal_common import WORK, MIN, DIGITS, record, finish, rounded_significant

PLACES = 30000
SCALE = fmpz(10)**PLACES

def fixed_places(x):
    assert x.is_finite() and x > 0 and x.rel_accuracy_bits() >= MIN
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    assert 0 < lo <= hi
    n = (2*lo.p*SCALE + lo.q)//(2*lo.q)
    assert 2*lo.p*SCALE > (2*n-1)*lo.q
    assert 2*hi.p*SCALE < (2*n+1)*hi.q
    s = str(n//SCALE)+"."+str(n%SCALE).zfill(PLACES)
    assert len(s.split(".")[1])==PLACES
    return {"decimal_places":PLACES,"relative_bits":x.rel_accuracy_bits(),
            "strict_half_ulp_rounding_cell":True,"rounded_decimal":s,
            "rounded_sha256":hashlib.sha256(s.encode("ascii")).hexdigest(),
            "lower_endpoint_exact":str(lo),"upper_endpoint_exact":str(hi)}

def main():
    pi = arb.pi()
    bp = arb(2).sqrt()/2
    a, g = arb(1), bp
    # For the exact iterates g_j <= AGM(1,b') <= a_j.
    # Enclose both endpoints; do not assume convergence from agreement
    # of rounded midpoint iterates.
    for i in range(25):
        a, g = (a+g)/2, (a*g).sqrt()
    lower = bp*pi/(2*a)
    upper = bp*pi/(2*g)
    agm = lower.union(upper)
    assert agm.is_finite() and agm > 0
    assert agm.rel_accuracy_bits() >= MIN
    print("AGM interval certified relative bits:",agm.rel_accuracy_bits(),flush=True)
    f0 = arb(40).sqrt().sqrt()*arb("0.25").gamma()/(4*pi.sqrt())
    gamma = (pi/5).sqrt()*f0**2
    assert gamma.is_finite() and gamma > 0 and gamma.rel_accuracy_bits()>=MIN
    # Independent exact rounding cell checks, plus overlap of the intervals.
    assert agm.lower().fmpq() <= gamma.upper().fmpq()
    assert gamma.lower().fmpq() <= agm.upper().fmpq()
    assert rounded_significant(agm)==rounded_significant(gamma)
    fa, fg = fixed_places(agm), fixed_places(gamma)
    assert fa["rounded_decimal"]==fg["rounded_decimal"]
    record("M13 T(1/sqrt(2)) AGM enclosure",agm)
    record("M13 T(1/sqrt(2)) M12 Gamma enclosure",gamma)
    finish("m13-cross-throat")
    result={"status":"CERTIFIED","source":"13/13.tex eq:cross-throatself",
            "working_bits":WORK,"required_relative_bits":MIN,
            "significant_digits":DIGITS,"decimal_places":PLACES,
            "distinct_quantities":1,"independent_evaluations":2,
            "values":[dict(name="AGM",**fa),dict(name="Gamma",**fg)]}
    Path("m13-cross-throat-fixed30000.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
    print("SUCCESS M13 CROSS THROAT AGM GAMMA STRICT AGREEMENT",flush=True)

if __name__=="__main__":
    main()
