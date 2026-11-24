"""M14.120 Prop. 4.4: exact-ball derived stationary dual and reciprocal curvature.
This verifies scalar evaluations, not the analytic identification with the conjugate.
"""
import argparse
import gzip
import json
from pathlib import Path
from flint import arb, fmpz, ctx

def ratio(a):
    m, e = a.man_exp()
    e = int(e)
    m = fmpz(m)
    if e >= 0:
        return m * fmpz(2)**e, fmpz(1)
    return m, fmpz(2)**(-e)

def rounding_cell(v, digits, exponent):
    scale = digits - 1 - exponent
    assert scale >= 0
    power = fmpz(10)**scale
    a = v.lower()
    b = v.upper()
    an, ad = ratio(a)
    bn, bd = ratio(b)
    # round positive values to nearest; strictly avoid either tie boundary
    al = 2*an*power + ad
    bl = 2*bn*power + bd
    lo = al // (2*ad)
    hi = bl // (2*bd)
    assert lo == hi, "interval straddles a decimal rounding cell"
    assert al > lo*2*ad and bl < (hi+1)*2*bd
    coefficient = str(lo)
    assert len(coefficient) == digits, "unexpected decimal exponent"
    return coefficient, str(a.man_exp()[0]), int(a.man_exp()[1]), str(b.man_exp()[0]), int(b.man_exp()[1])

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--bits", type=int, choices=[10000, 3600000], required=True)
    p.add_argument("--index", type=int, choices=[0,1,2], required=True)
    p.add_argument("--kind", choices=["dual","curvature"], required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    ctx.prec = args.bits
    assert ctx.prec == args.bits
    root = arb(2).sqrt()
    x = [1/(2*root), 1/root, root][args.index]
    s, c = x.sinh(), x.cosh()
    assert x > 0 and s > x
    if args.kind == "dual":
        v = x*c/s - 1 - (s/x).log()
        exp = [-2,-2,-1][args.index]
    else:
        v = x*x*s*s/(s*s-x*x)
        exp = 0
    assert v > 0
    digits, minbits = (2401,8182) if args.bits == 10000 else (1000001,3400000)
    accuracy = v.rel_accuracy_bits()
    assert accuracy >= minbits, (accuracy, minbits)
    coefficient, lm, le, um, ue = rounding_cell(v, digits, exp)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(working_bits=ctx.prec, relative_accuracy_bits=accuracy,
                   significant_digits=digits, rounded_coefficient=coefficient,
                   decimal_power=exp-digits+1, lower_dyadic=[lm,le], upper_dyadic=[um,ue],
                   index=args.index, kind=args.kind)
    with gzip.open(args.output, "wt", encoding="ascii") as f:
        json.dump(payload, f)
    print(f"PASS {args.kind} index={args.index} working_bits={ctx.prec} relative_bits={accuracy} strict_digits={digits} prefix={coefficient[:24]}")

if __name__ == "__main__":
    main()
