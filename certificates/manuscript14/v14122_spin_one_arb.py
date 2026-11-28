"""M14 v14.122: actual printed spin-one model, fixed fractional-decimal certificates.
Physical inputs are treated as exact model parameters, not measurements with million-place accuracy.
"""
import argparse, gzip, json, sys
from flint import arb, ctx, fmpz, fmpq, __version__
P=argparse.ArgumentParser()
P.add_argument("--index",type=int,choices=range(4),required=True)
P.add_argument("--model",choices=["printed","ideal"],required=True)
P.add_argument("--bits",type=int,default=3600000)
P.add_argument("--digits",type=int,default=1000001)
A=P.parse_args()
ctx.prec=A.bits
assert __version__=="0.9.0"
if hasattr(sys,"set_int_max_str_digits"): sys.set_int_max_str_digits(0)
root2=arb(2).sqrt()
x=[1/(2*root2),1/root2,arb(1),arb(13)/4][A.index]
# effective-to-saturation ratio: stated 2.64e-23/(2*9.274e-24), or ideal sqrt(2)
r=arb(6600)/4637 if A.model=="printed" else root2
L=x.cosh()/x.sinh()-1/x
q=r*L
assert q>0 and q<1, ("target is inside saturation",str(q))
y=(q+(4-3*q*q).sqrt())/(2*(1-q))
t=y.log()
assert t>0
# Check exact analytic inverse against the Arb enclosure.
assert ((y*y-1)/(y*y+y+1)-q).contains(0)
# k_B T/(2 mu_B) from printed constants: 1.380649e-23*293/(2*9.274e-24)
field=t*(arb(1380649)*293)/(arb(18548)*100)
classical=x*(arb(1380649)*293)/(arb(18548)*100*r)
increase=100*(field/classical-1)
values={"langevin":L,"target_over_saturation":q,"inverse_coupling":t,
        "classical_tesla":classical,"spin_one_tesla":field,"increase_percent":increase}
if A.model=="printed" and A.index==3:
    assert q>arb(98)/100 and field>arb(900) and field<arb(1100)
    print("MANUSCRIPT CONTRADICTION: target below saturation; finite field exists",flush=True)
scale=fmpz(10)**A.digits
def record(name,v):
    assert v.is_finite() and v>0
    bits=v.rel_accuracy_bits()
    assert bits>=A.bits-1000,(name,bits)
    lo,hi=v.lower().fmpq(),v.upper().fmpq()
    aa,bb=2*lo.p*scale,2*hi.p*scale
    m=(aa+lo.q)//(2*lo.q)
    assert aa>(2*m-1)*lo.q and bb<(2*m+1)*hi.q,(name,"rounding cell")
    digits=str(m).zfill(A.digits+1)
    rounded=digits[:-A.digits]+"."+digits[-A.digits:]
    print(name,"prefix",rounded[:27],"relative_bits",bits,"fractional digits",A.digits,"PASS",flush=True)
    return {"name":name,"relative_bits":bits,"fractional_digits":A.digits,
      "rounded":rounded,"lower_exact":str(lo),"upper_exact":str(hi)}
with gzip.open("m14-v14122-spin.json.gz","wt",compresslevel=1) as out:
    json.dump({"model":A.model,"index":A.index,"working_bits":A.bits,
        "python_flint":__version__,"records":[record(n,v) for n,v in values.items()]},out)
