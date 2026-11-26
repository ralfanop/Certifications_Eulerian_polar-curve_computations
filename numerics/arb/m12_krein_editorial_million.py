#!/usr/bin/env python3
"""M12 Krein section, exact source TeX SHA256
ebcb07619de560ef6b4be879bc5c084a6ab15cc7173ebebc2ad69e71bd1658be.
Strict fixed and significant decimal rounding of the explicit nonrational
parameters, angular norm, and spectral radius. Rational specializations
are checked exactly as rational arithmetic; the operator identities
themselves are not inferred from numerical agreement.
"""
import gzip, json, hashlib
from fractions import Fraction
from flint import arb, ctx, fmpz
from million_decimal_common import WORK, MIN, DIGITS, rounded_significant, record, finish

assert ctx.prec == WORK == 3600000 and MIN == 3400000 and DIGITS == 1000001
scale = fmpz(10)**DIGITS

def fixed(x):
    assert x.is_finite() and x > 0 and x.rel_accuracy_bits() >= MIN
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    a,b = 2*lo.p*scale, 2*hi.p*scale
    m = (a+lo.q)//(2*lo.q)
    assert a > (2*m-1)*lo.q and b < (2*m+1)*hi.q
    return str(m),str(lo),str(hi)

def match(x,y):
    assert x.overlaps(y)
    assert rounded_significant(x)==rounded_significant(y)
    assert fixed(x)[0]==fixed(y)[0]

s = arb(2).sqrt()
silver = 1+s
t1,t2 = silver.log(),arb(3).log()
angular = s-1
match(angular,(t1/2).tanh())
match(angular,(silver-1)/(silver+1))
match(silver,t1.exp())
match(silver,(1+angular)/(1-angular))
assert ((t2/2).tanh()).contains(arb(1)/2)
assert t2.exp().contains(arb(3))
assert (Fraction(3)-1)/(Fraction(3)+1)==Fraction(1,2)
assert (1+Fraction(1,2))/(1-Fraction(1,2))==3
vals = [
    ("eq:ul-krein-angular parameter log(1+sqrt(2))",t1),
    ("eq:ul-krein-angular parameter log(3)",t2),
    ("eq:ul-krein-angular norm sqrt(2)-1",angular),
    ("eq:ul-krein-radius e^t1 = 1+sqrt(2)",silver),
]
with gzip.open("m12-krein-fixed-endpoints.jsonl.gz","wt",compresslevel=1) as out:
    for name,x in vals:
        record(name,x)
        m,lo,hi=fixed(x)
        out.write(json.dumps(dict(name=name, fixed_decimal_places=DIGITS,
          relative_bits=x.rel_accuracy_bits(),rounded_scaled_integer=m,
          rounded_scaled_integer_sha256=hashlib.sha256(m.encode()).hexdigest(),
          lower_exact_dyadic=lo,upper_exact_dyadic=hi))+"\n")
        print(name,"1000001 fixed decimal places: PASS",flush=True)
finish("m12-krein-editorial")
print("EXACT RATIONAL SPECIALIZATIONS PASS 1/2, 3",flush=True)
