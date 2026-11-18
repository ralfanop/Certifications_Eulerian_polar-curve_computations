"""Independent midpoint Taylor integrals for M11 Eulerian arclength.

Uses the already audited zero-free disk |theta| <= 5 and polynomial
approximation of the entire speed square.  No panel depends on another.
"""
import argparse, json, math, resource, time
from pathlib import Path
from flint import arb, arb_poly, arb_series, fmpq, fmpz, ctx
from m11_euler_cauchy import analytic_disk, exact_endpoints


def panel(bits, target, panels, index):
    assert 0 <= index < panels
    assert bits > target + 64
    analytic_disk()
    ctx.prec = bits
    pi = arb.pi()
    h = pi / (2 * panels)
    c = (2 * index + 1) * h
    rho = h / (5 - c)
    assert 0 < rho < 1
    # Full length = twice sum of panels over [0,pi].
    # Use per-panel absolute budget, with extra guard bits.
    eta = arb(2)**(-target-32)
    assert 4/pi**2-eta > arb(1)/4 and eta < arb(1)/128
    # P in theta/5, using the entire even speed-square expansion.
    # Uniform error eta on |theta| <= 5, as in m11_euler_cauchy.
    a = arb(1)/24
    coeff = []
    k = 0
    while True:
        m = 2*k+4
        term = a*((3*m*(m-1))//2+2*m-2)
        if k >= 5 and 2*term.abs_upper() < eta:
            break
        coeff.extend((term, arb(0)))
        a = -25*a/((m+1)*(m+2))
        k += 1
    P = arb_poly(coeff)
    Q = P(arb_poly([c/5, h/5]))
    # Exact P is zero-free on |theta|<=5 by Rouché, and |sqrt P|<4.
    # Taylor coefficients of sqrt(P(c+h*x)) are bounded by 4*rho**j.
    # A symmetric panel integral drops all odd coefficients exactly.
    n = max(2, 2*math.ceil((target+64)/(-2*math.log2(float(rho)))))
    while 4*rho**n/(1-rho) >= arb(2)**(-target-32):
        n += 2
    ctx.cap = n
    print("panel",index,"/",panels,"degree",P.degree(),"order",n,"rho",rho.str(12),flush=True)
    s = arb_series(Q.coeffs()[:n], prec=n).sqrt()
    assert s.prec == n and s[0] > 0
    integral = arb(0)
    for j in range(0,n,2):
        integral += s[j]/(j+1)
    # Includes both +/-theta intervals.  Relative error is verified
    # independently after exact dyadic recombination.
    error = 4*h*(4*rho**n/(1-rho)+eta)
    value = 4*h*integral + arb(0,error.upper())
    assert value > 0 and value.rel_accuracy_bits() >= target
    return value


def read_endpoint(d):
    return fmpq(fmpz(d["numerator"]), fmpz(d["denominator"]))


def combine(bits, target, panels, paths):
    ctx.prec = bits
    lo, hi = fmpq(0), fmpq(0)
    seen = set()
    for path in paths:
        d = json.loads(Path(path).read_text())
        assert d["working_bits"] == bits and d["threshold_bits"] == target
        assert d["panels"] == panels and d["index"] not in seen
        assert 0 <= d["index"] < panels
        seen.add(d["index"])
        a, b = (read_endpoint(d["enclosure"][k]) for k in ("lower","upper"))
        assert 0 < a <= b
        lo += a
        hi += b
    assert seen == set(range(panels))
    value = arb((lo+hi)/2, arb((hi-lo)/2).upper())
    assert arb("5.5510") < value < arb("5.5511")
    assert value.rel_accuracy_bits() >= target
    return value


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--bits",type=int,required=True)
    p.add_argument("--target",type=int,required=True)
    p.add_argument("--panels",type=int,required=True)
    p.add_argument("--index",type=int)
    p.add_argument("--combine",nargs="+")
    p.add_argument("--output",required=True)
    a = p.parse_args()
    t = time.monotonic()
    x = combine(a.bits,a.target,a.panels,a.combine) if a.combine else panel(a.bits,a.target,a.panels,a.index)
    dt = time.monotonic()-t
    record = dict(working_bits=a.bits,threshold_bits=a.target,panels=a.panels,
                  index=a.index,enclosure=exact_endpoints(x),elapsed_seconds=dt,
                  peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(a.output).write_text(json.dumps(record,indent=2)+"\n")
    print("Eulerian length" if a.combine else "Panel",x.str(40),"relative bits",
          x.rel_accuracy_bits(),"seconds",dt,"peak RSS KiB",record["peak_rss_kib"],flush=True)
