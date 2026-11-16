#!/usr/bin/env python3
"""Figure 2 and §8 scalar audit for authoritative M15 2026-11-16.
Closed forms only; no analytic Dirichlet/CM theorem or operator realization is
proved by interval overlaps. Historical certificates are unchanged.
"""
import gzip
import json
from fractions import Fraction as Q
from pathlib import Path
from flint import arb, acb, ctx
from million_decimal_common import WORK, MIN, DIGITS, exact, record, finish

assert (WORK, MIN, DIGITS, ctx.prec) == (3600000, 3400000, 1000001, 3600000)
source = "9b4f15263894f25d3d5ddc29f8cdb839c53e9fcf31115642ed967b4c75aab09b"
# Dyadic endpoints are retained in addition to the shared rounded digits and ball.
def certify(name, x):
    assert x.rel_accuracy_bits() >= MIN, name
    record(name, x)
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    endpoint_stream.write(json.dumps({"name":name,
        "lower":[str(lo.p),str(lo.q)], "upper":[str(hi.p),str(hi.q)]})+"\n")

exact_values = {
    "disk centre real": Q(0), "disk centre imaginary": Q(1),
    "disk radius": Q(1,2), "bottom point real": Q(0),
    "bottom point imaginary": Q(1,2), "top point imaginary": Q(3,2),
    "z0 real": Q(0), "z1 real": Q(0),
    "boundary |1-z^2|": Q(5,4), "x*": Q(1,20), "x0": Q(1,8),
    "support radius": Q(2), "pushforward support endpoint": Q(4),
    "analytic disk radius": Q(1,4), "critical scale": Q(1,12),
    "sinh(log(phi))": Q(1,2)
}
assert 1+exact_values["disk radius"]**2 == exact_values["boundary |1-z^2|"]
assert exact_values["x0"] == Q(1,2)/4
assert exact_values["top point imaginary"] == 1+Q(1,2)
pi = arb.pi()
r2, r5 = arb(2).sqrt(), arb(5).sqrt()
z0, z1 = 1/r2, r2
phi = (1+r5)/2
logphi = phi.log()
L0 = 2/r5
chi5 = 2*logphi/r5
chi8 = pi/arb(8).sqrt()
xstar = exact(Q(1,20))
x0 = exact(Q(1,8))
G = lambda x: 1/(1-4*x).sqrt()
factorial_moment = 12*xstar*xstar / ((1-4*xstar)**2*(1-4*xstar).sqrt())
theta2 = 2*x0*(1+2*x0)/((1-4*x0)**2*(1-4*x0).sqrt())
halfangle = exact(Q(1,2)).atan()
tanh = logphi.tanh()
sech = 1/logphi.cosh()
assert (z0*z1).contains(1)
assert z0 > exact(Q(1,2)) and z0 < 1 and z1 > 1 and z1 < exact(Q(3,2))
assert L0.overlaps(chi5/logphi) and L0.overlaps(sech) and L0.overlaps(halfangle.cos())
assert G(xstar).overlaps(r5/2) and G(xstar).overlaps(1/L0)
assert factorial_moment.overlaps(3*r5/128)
assert theta2.overlaps(5/arb(8).sqrt()) and theta2.overlaps(10*z0**5)
assert theta2.overlaps(5*chi8/pi)
assert (L0*theta2).overlaps(exact(Q(5,2)).sqrt())
assert tanh.overlaps(1/r5)
cL = r5/12
assert cL.overlaps(1/(12*tanh)) and cL.overlaps((phi**2+1)/(12*(phi**2-1)))
assert cL > exact(Q(1,12))
values = {
 "Figure 2 / z0 imaginary": z0, "Figure 2 / z1 imaginary": z1,
 "Figure 2 / L0": L0, "phi": phi, "log(phi)": logphi,
 "L(1,chi5) closed form": chi5, "L(1,chi-8) closed form": chi8,
 "Krivine upper bound": pi/(2*(1+r2).log()),
 "G_Cat(1/20)": G(xstar), "factorial moment at 1/20": factorial_moment,
 "c_L": cL, "t_L": tanh, "p_infinity(c_L) closed form": 1/G(xstar),
 "alpha_3 = alpha_5 in radians": 2*halfangle,
 "theta2 G_Cat(1/8)": theta2, "10 c_E": 10*z0**5,
 "L0 theta2 G_Cat(1/8)": L0*theta2, "sqrt(5/2)": exact(Q(5,2)).sqrt(),
}
# j evaluated independently at both imaginary-axis arguments. Inclusion of
# 8000 is only a verification of consistency with the exact CM theorem;
# it is not an inference of exact equality from interval arithmetic.
import os
mode = os.environ.get("M15_FIGURE_MODE", "scalar")
with gzip.open("m15-figure2-exact-endpoints.jsonl.gz","wt",encoding="utf-8",compresslevel=1) as endpoint_stream:
    if mode == "modular":
        for name, y in (("z0",z0),("z1",z1)):
            j = acb(0,y).modular_j()
            assert j.is_finite() and j.real.contains(8000) and j.imag.contains(0)
            certify("Figure 2 / Re j("+name+") numerical enclosure",j.real)
    else:
        assert mode == "scalar"
        for name,x in values.items():
            certify(name,x)
Path("m15-figure2-exact.json").write_text(json.dumps({
    "source_zip_sha256":source,
    "mode":mode,
    "exact_rationals": {name:[str(q.numerator),str(q.denominator)] for name,q in exact_values.items()},
    "justification":"Coordinates and scales by definitions; boundary norm by (i/2)^2=-1/4; x0 by z0^2=-1/2; sinh(log(phi))=(phi-1/phi)/2=1/2.",
    "j_claim":"8000 is the stated exact CM integer; modular mode tests consistency, not exact equality or exact imaginary zero.",
    "not_proved_by_arb":["CM theorem", "analytic Dirichlet L evaluations", "arcsine moments", "operator resolvent", "holomorphic graph", "sharp Lipschitz theorem"]
},indent=2),encoding="utf-8")
finish("m15-figure2-"+mode)
