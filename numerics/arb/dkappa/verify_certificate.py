"""Check stored certificate consistency and rounding using exact rational arithmetic.

This is a record checker; the accompanying proof and certify_dk.py establish
that the intervals enclose the mathematical quantity.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
root=Path(__file__).resolve().parent
def require(x,msg):
    if not x:raise SystemExit(msg)
def interval(obj):
    a,b=Q(obj["lower"]),Q(obj["upper"])
    require(a<=b,"Reversed interval")
    return a,b
records=[json.loads((root/n).read_text()) for n in
         ["D_K_CERTIFICATE_32_64.json","D_K_CERTIFICATE_40_128.json"]]
digest=hashlib.sha256((root/"certify_dk.py").read_bytes()).hexdigest()
target=Q("0.203783759536049443826081")
cell=(target-Q(1,2*10**24),target+Q(1,2*10**24))
outer=(Q("0.203783759536049443826080629422606828"),
       Q("0.203783759536049443826080629422606829"))
for r in records:
    require(r["script_sha256"]==digest,"Certificate program hash mismatch")
    lo,hi=interval(r["D"])
    require(0<lo<=hi,"D must be positive")
    require(cell[0]<lo<=hi<cell[1],"24-place rounding cell failed")
    require(outer[0]<lo<=hi<outer[1],"Short printed enclosure failed")
    slo,shi=interval(r["D_squared"])
    require(slo>0 and lo*lo<=shi and hi*hi>=slo,"Square/root records inconsistent")
    for c in r["rounding_checks"]:
        q=Q(c["rounded"]);h=Q(1,2*10**c["places"])
        require(c["certified"] and q-h<lo<=hi<q+h,
                "Recorded rounding test failed at "+str(c["places"])+" places")
a,b=interval(records[0]["D"]);c,d=interval(records[1]["D"])
require(a<=c<=d<=b,"Finer certificate not contained in principal certificate")
ref=json.loads((root/"DIRECT_REFERENCE_CHECK.json").read_text())
last=ref["results"][-1]
require(last["gauss_order"]==64,"Missing independent order-64 result")
require(a<Q(last["D"])<b,"Independent quadrature outside principal certificate")
for key in ["E","L"]:
    a,b=interval(records[0]["half_lengths"][key])
    require(a<Q(ref["half_lengths"][key])<b,"Independent half-length mismatch")
print("PASS: both certificates support the existing 24-place value.")
print("PASS: all recorded rounding tests, short enclosure and program hashes.")
print("PASS: finer interval is contained in the principal interval.")
print("PASS: independent direct quadrature lies inside the principal interval.")
