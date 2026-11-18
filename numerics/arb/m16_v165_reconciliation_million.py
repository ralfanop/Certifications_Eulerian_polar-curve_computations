"""M16 v16.5 definitive-source reconciliation and §14 scalar benchmarks."""
import gzip
import json
import subprocess
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish

ctx.prec = 3600000
assert (ctx.prec, WORK, MIN, DIGITS) == (3600000, 3600000, 3400000, 1000001)
head = subprocess.check_output(["git","rev-parse","HEAD"], text=True).strip()
pi = arb.pi()
z2 = pi**2/6
z4 = pi**4/90
z6 = pi**6/945
z8 = pi**8/9450

# #301 historical spatial block, NOT #306 periodic mixed block.
dirac = pi**2-pi**4/12
spatial_maxwell = 2*(z6-z8)
values = {
    "eq_ktrace2_spatial_transverse": 2*(z2-z4),
    "eq_diracfourthzeta": dirac,
    "eq_fourthtrace_spatial_maxwell_component": spatial_maxwell,
    "eq_fourthtrace_total_spatial": dirac+spatial_maxwell,
}
old_centres = {
    "eq_ktrace2_spatial_transverse": 1125221666274,
    "eq_diracfourthzeta": 1752180148256,
    "eq_fourthtrace_spatial_maxwell_component": 26531411573,
    "eq_fourthtrace_total_spatial": 1778711559829,
}
for name, centre in old_centres.items():
    assert abs(values[name]-arb(centre)/10**12) < arb(1)/(2*10**12), name

# Chosen scalar benchmarks for equations 151–174; not a claim about
# the magnetic Schrödinger operator or actual optimal couplings.
for suffix,x in [("invsqrt2",1/arb(2).sqrt()),("sqrt2",arb(2).sqrt())]:
    q = (-2*x).exp()
    a = (-x).exp()
    zm = a/(1-q)
    zM = 4*a*(3-q)/(1-q)**3
    w1 = 4*q/(1-q)-2*q/(3-q)
    profile = 2*x*zm
    # independent formula evaluations: positive rigorous overlap only;
    # equalities themselves are mathematical obligations.
    assert (1/(2*x.sinh())).overlaps(zm)
    b = (2*x).exp()
    assert (4*(3*x).exp()*(3*b-1)/(b-1)**3).overlaps(zM)
    assert (4/(b-1)-2/(3*b-1)).overlaps(w1)
    assert (x/x.sinh()).overlaps(profile)
    for k,y in {"q":q,"Zm":zm,"ZM":zM,"W1_formula":w1,"Euler_profile_inverse":profile}.items():
        values[k+"_"+suffix] = y

with gzip.open("m16-v165-reconciliation-endpoints.jsonl.gz","wt",encoding="utf-8") as f:
    for name, x in values.items():
        assert ctx.prec == 3600000
        assert x.is_finite() and x > 0, name
        assert x.rel_accuracy_bits() >= 3400000, (name,x.rel_accuracy_bits())
        record(name,x)
        f.write(json.dumps({"name":name,"head":head,"lower":str(x.lower().fmpq()),
            "upper":str(x.upper().fmpq()),"relative_bits":x.rel_accuracy_bits()})+"\n")
finish("m16-v165-reconciliation")
