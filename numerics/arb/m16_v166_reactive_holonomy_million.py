#!/usr/bin/env python3
"""M16 v16.6 strict million-digit scalar benchmarks, not operator proofs."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import json
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish

assert (WORK, MIN, DIGITS, ctx.prec) == (3600000,3400000,1000001,3600000)
SOURCE = "ed3877cbb2250598bda640ca05ddb69194f4b0675db165cc7dcc94fd71796cc3"
# All rational benchmark inputs/outputs below are exact, not relative-bit claims.
# TE epsilon=mu=omega=X=1, beta=1, squared normalised amplitude A=2.
assert Q(1)*Q(1)/Q(1)==1
assert Q(2)*Q(1)*Q(1)/Q(2)==1
assert -Q(2)/2 == -2*Q(1)*Q(1,2)
assert Q(1,4*2)==Q(1,8)
Path("m16-v166-exact.json").write_text(json.dumps({
  "source_zip_sha256":SOURCE,
  "TE_unit_parameters":{"epsilon":"1","mu":"1","omega":"1","X":"1",
    "beta":"1","kappa_squared":"2","A_at_boundary":"2",
    "magnetic_excess_at_boundary":"1","integrated_excess":"1/2",
    "imaginary_z_flux_at_boundary":"-1","real_z_flux":"0"},
  "scalar_moment_b_2":"1/8",
  "zero_holonomy_product":"1",
  "scope":"exact rational arithmetic and analytic formulas; no relative precision for exact zero"
},indent=2),encoding="utf-8")

with gzip.open("m16-v166-endpoints.jsonl.gz","wt",encoding="utf-8",compresslevel=1) as out:
    def certify(name,v):
        assert v.is_finite() and not v.contains(0), name
        assert v.rel_accuracy_bits() >= MIN,(name,v.rel_accuracy_bits())
        record(name,v)
        l,h=v.lower().fmpq(),v.upper().fmpq()
        out.write(json.dumps({"name":name,"lower":[str(l.p),str(l.q)],
          "upper":[str(h.p),str(h.q)]})+"\n")
        out.flush()

    # Positive shift benchmarks x=pi*a=1/sqrt(2) and sqrt(2).
    # This is an explicit choice for testing the general formula, not
    # a decimal value printed in the source manuscript.
    pi=arb.pi()
    sqrt2=arb(2).sqrt()
    certify("TE unit-parameter tangential kappa",sqrt2)
    q=(-arb(2)).exp()
    certify("TE unit-parameter squared decay multiplier at z=1",q)
    certify("TE unit-parameter longitudinal real flux at z=1",sqrt2*q)
    certify("TE unit-parameter imaginary normal flux at z=1",-q)
    certify("TE unit-parameter magnetic excess at z=1",q)
    for label,x in (("x=1/sqrt(2)",1/sqrt2),("x=sqrt(2)",sqrt2)):
        a=x/pi
        s=(2*x).sinh()
        c=(2*x).cosh()
        m0=pi/(4*a)*s/(c-1)
        mh=pi/(4*a)*s/(c+1)
        dh=(c+1)/(c-1)
        ratio=mh/m0
        tanh2=(x.sinh()/x.cosh())**2
        profile1=x.sinh()/x
        profile2=s/(2*x)
        euler=x**2*profile1**4/profile2**2
        assert ratio.overlaps(tanh2) and ratio.overlaps(euler)
        assert ratio.overlaps(1/dh)
        assert ratio>0 and ratio<1
        for name,v in (
            ("shift a",a),("M_0",m0),("M_half",mh),
            ("D_half",dh),("M_half/M_0",ratio),
            ("tanh(x)^2",tanh2),("Eulerian expression",euler),
            ("reciprocal D_half",1/dh),
        ):
            certify(label+" "+name,v)
finish("m16-v166-reactive-holonomy")
