"""M14 inverse spectral rigidity: strict Arb enclosures and decimal rounding.
Only the scalar finite-data criterion is certified here, conditional on the
analytic theorem and its data/trace hypotheses. No unknown spectrum is sampled.
"""
import argparse
import gzip
import json
import math
import sys
from pathlib import Path
from flint import arb, fmpz, ctx

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

LEVELS = {32000: (9000, 30000), 300000: (30000, 100000),
          3600000: (1000001, 3400000)}
NAMES = ("amplification", "data", "remainder", "budget", "threshold",
         "margin", "rational_bound", "lambda1_lo", "lambda1_ref",
         "lambda1_hi", "lambda2_lo", "lambda2_ref", "lambda2_hi")

def chebyshev(n, x):
    a, b = arb(1), x
    if n == 0:
        return a
    for _ in range(1, n):
        a, b = b, 2*x*b-a
    return b

def ratio(a):
    m, e = a.man_exp()
    m, e = fmpz(m), int(e)
    if e >= 0:
        return m * fmpz(2)**e, fmpz(1)
    return m, fmpz(2)**(-e)

def rounded_certificate(v, digits, minbits):
    assert v > 0
    accuracy = v.rel_accuracy_bits()
    assert accuracy >= minbits, (accuracy, minbits)
    # Float only proposes a decimal exponent; exact ball comparisons verify it.
    exponent = math.floor(math.log10(float(v)))
    assert v > arb(10)**exponent and v < arb(10)**(exponent+1)
    scale = digits - 1 - exponent
    assert scale >= 0
    power = fmpz(10)**scale
    lo, hi = v.lower(), v.upper()
    an, ad = ratio(lo)
    bn, bd = ratio(hi)
    al, bl = 2*an*power+ad, 2*bn*power+bd
    qlo, qhi = al//(2*ad), bl//(2*bd)
    assert qlo == qhi, "interval crosses a decimal rounding boundary"
    assert al > qlo*2*ad and bl < (qhi+1)*2*bd, "rounding tie not excluded"
    coefficient = str(qlo)
    assert len(coefficient) == digits
    lm, le = lo.man_exp()
    um, ue = hi.man_exp()
    return dict(working_bits=ctx.prec, relative_accuracy_bits=accuracy,
                significant_digits=digits, decimal_power=exponent-digits+1,
                rounded_coefficient=coefficient,
                lower_dyadic=[str(lm), int(le)], upper_dyadic=[str(um), int(ue)])

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--bits", type=int, choices=sorted(LEVELS), default=3600000)
    p.add_argument("--quantity", choices=("all",)+NAMES, default="all")
    p.add_argument("--output", type=Path, default=Path("out/inverse-spectral"))
    args=p.parse_args()
    ctx.prec=args.bits
    assert ctx.prec == args.bits
    digits, minbits=LEVELS[args.bits]
    N, M = 32, 2
    h, S, delta = arb(1), arb(1)/5, arb(1)/100
    eta = arb(1)/arb(10)**74
    pi=arb.pi()
    rho=M*pi+delta
    Q=rho**2
    assert Q > h
    amplification=chebyshev(N,1+2*Q/h)
    data=eta*amplification
    remainder=2*(S*Q).exp()*(S*(Q+h))**(N+1)/math.factorial(N+1)
    budget=data+remainder
    threshold=delta.sin()/rho
    assert data > 0 and remainder > 0
    assert budget < threshold
    assert Q < 40 and rho < arb(63)/10 and arb(8).exp() < 3000
    rational_bound=arb(162)**32/arb(10)**74+6000*(arb(41)/5)**33/math.factorial(33)
    assert rational_bound < arb(3)/2000
    assert arb(3)/2000 < (delta-delta**3/6)/(arb(63)/10)
    assert (delta-delta**3/6)/(arb(63)/10) < threshold
    values=dict(amplification=amplification, data=data, remainder=remainder,
                budget=budget, threshold=threshold, margin=threshold-budget,
                rational_bound=rational_bound)
    for n in range(1,M+1):
        lo=1/(n*pi+delta)**2
        hi=1/(n*pi-delta)**2
        ref=1/(n*pi)**2
        assert lo < ref and ref < hi
        values.update({f"lambda{n}_lo":lo, f"lambda{n}_ref":ref, f"lambda{n}_hi":hi})
    assert set(values) == set(NAMES)
    args.output.mkdir(parents=True, exist_ok=True)
    print("working_bits",ctx.prec, "required_relative_bits",minbits,
          "required_significant_digits",digits, flush=True)
    for name in NAMES if args.quantity=="all" else (args.quantity,):
        v=values[name]
        cert=rounded_certificate(v,digits,minbits)
        cert.update(quantity=name, N=N, M=M, h="1", S="1/5",
                    delta="1/100", eta="1e-74",
                    scope="conditional scalar localization criterion")
        with gzip.open(args.output / f"{name}.json.gz", "wt", encoding="ascii") as out:
            json.dump(cert,out,separators=(",",":"))
        print("PASS",name,v.str(50),"relative_bits",cert["relative_accuracy_bits"],
              "strict_digits",digits,flush=True)
    print("PASS strict interval inequalities and decimal rounding",flush=True)

if __name__=="__main__":
    main()
