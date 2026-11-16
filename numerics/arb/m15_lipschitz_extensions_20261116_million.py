#!/usr/bin/env python3
"""M15 new §8 extensions: exact rational data and nonzero scalar checks.
These are finite examples, not proofs of metric asymptotics or PDE spectra.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import gzip, json
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, record, finish, exact

assert (WORK, MIN, DIGITS, ctx.prec) == (3600000,3400000,1000001,3600000)
source = "245496a6fe9ad5ba20156c726d4b334451667c90c54078073c3a46bde651e64b"
exact_data = {
 "optimal exponent": Q(2,3), "cross-branch Jensen exponent":Q(1,3),
 "outer coefficient relative to a*v":Q(4),
 "X prime coefficient relative to a*v":Q(6),
 "Y prime coefficient relative to a":Q(1),
 "inner coefficient relative to a":Q(1),
 "cross-branch integral coefficient relative to C":Q(1,2),
 "channel at x=0":Q(1)
}
rows = []
# Exact checks for examples of the alternating-binomial coupling (R=1).
# The symbolic Pascal proof is a different Lean obligation.
for N in range(2,65,2):
    q = Q(1,2**(N-1))
    x = [Q(-1)+Q(2*j,N) for j in range(N+1)]
    p = [q*comb(N,j) if j%2==0 else Q(0) for j in range(N+1)]
    m = [q*comb(N,j) if j%2==1 else Q(0) for j in range(N+1)]
    assert sum(p)==sum(m)==1
    assert p==p[::-1] and m==m[::-1]
    assert sum(w*y for w,y in zip(p,x))==sum(w*y for w,y in zip(m,x))==0
    lhs=[Q(0)]*(N+1); rhs=lhs.copy(); cost=Q(0)
    for j in range(N):
        w=q*comb(N-1,j)
        i,k=(j,j+1) if j%2==0 else (j+1,j)
        lhs[i]+=w; rhs[k]+=w; cost+=w*abs(x[i]-x[k])
    assert lhs==p and rhs==m and cost==Q(2,N)
    assert all(abs(x[i]-x[k])>=Q(2,N)
        for i in range(0,N+1,2) for k in range(1,N,2))
    rows.append({"N":N,"R":"1","exact_transport_cost":str(cost),
        "proof":"Pascal marginals, unit mass, support separation and explicit neighbor coupling"})
Path("m15-lipschitz-extensions-exact.json").write_text(json.dumps({
 "source_zip_sha256":source,
 "exact_constants":{k:[str(v.numerator),str(v.denominator)] for k,v in exact_data.items()},
 "exact_finite_examples":rows,
 "scope":"exact rational arithmetic, not relative-bit claims for zeros/rationals"
},indent=2),encoding="utf-8")

# Universal irrational coefficient of the cross-branch estimate and
# illustrative normalized values at a=v=R=T=ell=x=1.
# The general a,v,R,T,ell,x-dependent formulas are not a finite list of scalars.
r2=(arb(2).log()/3).exp()
assert (r2**3).contains(2)
k=1/(r2**4)
assert (k**3).contains(exact(Q(1,16)))
with gzip.open("m15-lipschitz-extensions-endpoints.jsonl.gz","wt",encoding="utf-8",compresslevel=1) as out:
    def certify(name,x):
        assert x.rel_accuracy_bits() >= MIN, (name,x.rel_accuracy_bits())
        record(name,x)
        l,h=x.lower().fmpq(),x.upper().fmpq()
        out.write(json.dumps({"name":name,"lower":[str(l.p),str(l.q)],
            "upper":[str(h.p),str(h.q)]})+"\n")
    certify("cross-branch coefficient 2^(1/3)",r2)
    certify("cusp limit coefficient at a=v=1 (example)",k)
    for N in (2,4):
        y=(exact(Q(1,N))).sin()
        d=2*(-1)**(N//2)*y**N
        dd=arb(0)
        for j in range(N+1):
            dd += (-1)**j*comb(N,j)*exact(Q(-1)+Q(2*j,N)).cos()
        dd *= exact(Q(1,2**(N-1)))
        assert d.overlaps(dd)
        certify(f"alternating characteristic difference R=t=1,N={N} (example)",d)
        certify(f"independent finite cosine sum R=t=1,N={N} (example)",dd)
    certify("shifted channel determinant at ell=x=1 (example)",arb(1).sinh())
finish("m15-lipschitz-extensions")
