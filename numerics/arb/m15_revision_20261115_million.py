#!/usr/bin/env python3
"""M15 15-Nov Discussion-First revision: new finite table and spectral scalars.

Authoritative ZIP SHA256:
0c80a4bc28f99b20239d8640f9ed29d53640309998a05e92c24b0d0fe1ba3ec7
Source labels: Table 1, eq:terminal-lagrange-leading,
eq:terminal-lagrange-relative, eq:hopf-fibre-det, eq:terminal-reg-product,
eq:terminal-laurent. Uses #318's strict dyadic endpoint rounding checker.
This is a finite closed-expression audit, not spectral zeta continuation,
Lagrange inversion, an asymptotic proof, or Thue-Morse individual sectors.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
from flint import arb, ctx
from million_decimal_common import WORK, MIN, DIGITS, exact, record, finish

assert (WORK, MIN, DIGITS) == (3600000, 3400000, 1000001)
assert ctx.prec == WORK
pi = arb.pi()
exact_records = []

def rational(name, x):
    x = Q(x)
    exact_records.append({"name": name, "numerator": str(x.numerator),
                          "denominator": str(x.denominator),
                          "method": "exact integer/rational arithmetic"})
    return x

table = {
    16: ([1,65519,41932745,3572085255,85383238549,782115518299,
          3207483178157,6382798925475,6382798925475,3207483178157,
          782115518299,85383238549,3572085255,41932745,65519,1],
         "111.186330312023"),
    17: ([1,131054,126781020,14875399450,473353301060,5717291972382,
          31055652948388,83137223185370,114890380658550,83137223185370,
          31055652948388,5717291972382,473353301060,14875399450,
          126781020,131054,1], "63.789108310559"),
}
row = [1]
for n in range(2, 18):
    old = row
    row = [(k+1)*(old[k] if k < len(old) else 0) +
           (n-k)*(old[k-1] if k else 0) for k in range(n)]
    if n not in table:
        continue
    assert row == table[n][0] and row == row[::-1]
    assert all(c > 0 for c in row) and sum(row) == factorial(n)
    weights = [Q(c, factorial(n)) for c in row]
    xs = [Q(k+1, n+1) for k in range(n)]
    mean = sum(w*x for w,x in zip(weights, xs))
    var = sum(w*(x-Q(1,2))**2 for w,x in zip(weights, xs))
    assert mean == Q(1,2) and var == Q(1,12*(n+1))
    rational(f"n={n} mean", mean)
    rational(f"n={n} variance", var)
    for k,c in enumerate(row):
        rational(f"n={n} row[{k}]", c)
    m = n//2
    if n % 2:
        slope = Q((n+1)*(row[m]-row[m-1]), factorial(n))
        assert 0 < slope < 2
        rad = 2*(1/exact(slope)).atan()
    else:
        assert row[m-1] == row[m]
        slope = Q((n+1)*(row[m-1]-row[m-2]), factorial(n))
        assert slope > 0
        rad = pi-exact(slope).atan()
    rational(f"n={n} central slope", slope)
    deg = rad*180/pi
    assert abs(deg-exact(Q(table[n][1]))) < exact(Q(1,2*10**12))
    record(f"n={n} angle radians",rad)
    record(f"n={n} angle degrees",deg)

# Closed scalar targets of the new spectral and terminal propositions.
A = 4*pi*pi
assert A > 1
record("Hopf fibre scalar 4*pi^2",A)
logA = A.log()
record("log(4*pi^2)",logA)
record("Laurent coefficient log(A)/12",logA/12)
reg = (-logA/12).exp()
assert reg > 0 and reg < 1
record("generalised terminal product A^(-1/12)",reg)
# Interval overlap is only a cross-check, not a proof of the identity.
assert (reg**12 * A).contains(1)
for M in (2,3,4,5,8):
    gamma = rational(f"M={M} gamma_M", 1 if M == 2 else 1-M)
    b = 1/(2*A**(M-1))
    b_independent = (2*pi)**(2-2*M)/2
    assert b > 0 and b.overlaps(b_independent)
    c = exact(gamma)/pi
    record(f"M={M} b_(M,2M)",b)
    record(f"M={M} relative correction gamma_M/pi",c)
    record(f"M={M} b_(M,2M+1)",b*c)
    record(f"M={M} scaled reciprocal a_M",A**(M-1))

Path("m15-revision-exact.json").write_text(json.dumps({
    "source_zip_sha256":"0c80a4bc28f99b20239d8640f9ed29d53640309998a05e92c24b0d0fe1ba3ec7",
    "exact_records":exact_records,
    "scope":"finite rows, rational slopes and scalar terminal expressions only",
    "not_certified_here":["all-order analytic jets","squarefree Fredholm infinite product",
      "individual Thue-Morse determinants and Flajolet-Martin constant",
      "spectral zeta analytic continuation","angle limit and original figure"],
},indent=2),encoding="utf-8")
finish("m15-revision-20261115")
