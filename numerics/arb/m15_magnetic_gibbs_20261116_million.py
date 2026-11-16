#!/usr/bin/env python3
"""M15 authoritative 20261116 magnetic Gibbs and intervening geometric extensions.
Scalar enclosures of closed formulas only; not a proof of spectral convergence.
"""
import gzip
import json
import sys
from pathlib import Path
from fractions import Fraction as Q
from flint import arb, ctx, fmpz, fmpq
from million_decimal_common import WORK, MIN, DIGITS, record, finish, exact

assert (ctx.prec, WORK, MIN, DIGITS) == (3600000, 3600000, 3400000, 1000001)
SOURCE = "7b2476cb99b68fe7322efbd3d4eb14ea8eb35019399d6eba13745094fa3cfc41"
mode = sys.argv[1]
assert mode in ("magnetic", "geometry")
label = "m15-gibbs-" + mode
assertions = []

def verify_printed(name, value, printed):
    """Strict containment in the printed 50-place nearest rounding cell."""
    assert len(printed.split(".")[1]) == 50
    n = fmpz(printed.replace(".", ""))
    den = 2 * fmpz(10)**50
    lo, hi = value.lower().fmpq(), value.upper().fmpq()
    assert fmpq(2*n-1, den) < lo <= hi < fmpq(2*n+1, den), name
    assertions.append({"name":name,"printed_50_places":printed,"strict_cell":True})

with gzip.open(label+"-endpoints.jsonl.gz","wt",encoding="utf-8",compresslevel=1) as out:
    def certify(name,v,printed=None):
        assert v.is_finite() and not v.contains(0), name
        assert v.rel_accuracy_bits() >= MIN, (name,v.rel_accuracy_bits())
        if printed is not None:
            verify_printed(name,v,printed)
        record(name,v)
        lo,hi=v.lower().fmpq(),v.upper().fmpq()
        out.write(json.dumps({"name":name,"lower":[str(lo.p),str(lo.q)],
                              "upper":[str(hi.p),str(hi.q)]})+"\n")
    if mode == "magnetic":
        a=1/arb(8).sqrt()
        b=1/arb(2).sqrt()
        assert (2*a).overlaps(b)
        for n,x,p1,p2 in [
          ("a",a,"0.50514404235910598133179797642641412865198380448805",
                 "0.58208553300559051545604864104846029987534647497147"),
          ("b",b,"0.51984182914554522828164803877243627920338910304217",
                 "0.59543909938728900171380288132459176482717017334995")]:
            r=(-2*x).exp()
            e=(-x).exp()
            sh=x.sinh()
            coth=x.cosh()/sh
            L=coth-1/x
            Lprime=1/x**2-1/sh**2
            z=1/(2*sh)
            w1=1-(1-e)/(1+e)/x
            w2sq=1-2*L/x
            w2=w2sq.sqrt()
            assert w1.overlaps(1-(x/2).tanh()/x)
            assert w2sq.overlaps(1-2*(1+r)/(1-r)/x+2/x**2)
            assert z.overlaps(e/(1-r))
            assert L > 0 and Lprime > 0 and w1 > 0 and w2sq > 0
            assert w1 < w2 and w2 < 1
            for name,v in [
                ("x",x),("Im z",2*x),("Gibbs ratio exp(-2x)",r),
                ("first atom weight",1-r),("limit partition trace",z),
                ("normalised trace",2*x*z),("Eulerian imaginary profile",sh/x),
                ("exponential mean",1/x),("discrete mean",coth),
                ("mean difference",L),("exponential variance",1/x**2),
                ("discrete variance",1/sh**2),("variance difference",Lprime),
                ("W2 squared",w2sq)]:
                certify(n+" "+name,v)
            certify(n+" W1",w1,p1)
            certify(n+" W2",w2,p2)
    else:
        pi=arb.pi()
        q=2/pi
        aH=(1-q)/2
        l8=pi/arb(8).sqrt()
        l2=pi**2/8
        z3=arb(3).zeta()
        l5=exact(Q(124,125))*z3
        w1=q-exact(Q(1,2))
        w2sq=exact(Q(5,6))-2*q*q
        w2=w2sq.sqrt()
        wi=(1-q*q).sqrt()-q*q.acos()
        d5=exact(Q(5,6))*l5-1/l2
        assert (l8*l8).overlaps(l2)
        assert w2sq.overlaps(exact(Q(1,3))-2*w1-2*w1*w1)
        assert d5.overlaps(w2sq+exact(Q(5,6))*(l5-1))
        assert w1 > 0 and w1 < w2 and w2 < wi
        for name,v in [("q",q),("limacon coefficient",aH),("L(1,chi_-8)",l8),
                       ("L2(2)",l2),("L2 reciprocal",1/l2),("zeta(3)",z3),
                       ("L5(3)",l5),("cross integral",4/pi**2),
                       ("max displacement location",q*q.acos())]:
            certify(name,v)
        certify("uniform-arcsine W1",w1,"0.13661977236758134307553505349005744813783858296183")
        certify("uniform-arcsine W2",w2,"0.15087698364770937381074949892522371428684630516813")
        certify("uniform-arcsine W infinity",wi,"0.21051366235301868432776943515583366338518237303085")
        certify("uniform-arcsine W2 squared",w2sq,"0.02276386419463116178229762765551222209846313595536")
        certify("D5",d5,"0.18313090413989577104608117450497754779751847095684")

# Exact rational statements, not relative accuracy of an exact result.
if mode=="magnetic":
    exact_data={"limiting W infinity":Q(1),"cell width":Q(2),
                "first level":Q(1),"trace normalization factor relative to x":Q(2)}
else:
    exact_data={"Schwarzian majorant":Q(17,50),"Ahlfors-Weill k":Q(17,100),
                "dilatation upper bound":Q(117,83),"Kahler inf":Q(4,13),
                "Kahler sup":Q(4,5),"interior Jacobian":Q(1,2),
                "L2 Euler factor":Q(3,4),"L5 Euler factor":Q(124,125)}
    assert Q(1,4)*Q(17,8)*Q(16,25)==Q(17,50)
    assert (1+Q(17,100))/(1-Q(17,100))==Q(117,83)
    assert 1/(1+Q(3,2)**2)==Q(4,13)
    assert 1/(1+Q(1,2)**2)==Q(4,5)
Path(label+"-source.json").write_text(json.dumps({
    "source_zip_sha256":SOURCE,"printed_checks":assertions,
    "exact_rational_constants":{k:str(v) for k,v in exact_data.items()},
    "scope":"closed scalar formulas and exact rational arithmetic; analytic proofs separate"
},indent=2),encoding="utf-8")
finish(label)
