#!/usr/bin/env python3
"""Generate UniformLanczos/HigherProfileCoefficients.lean (Task L4)."""
from fractions import Fraction as Fr
from math import factorial
import sys
from l4_series import Lp, Ip, phiA, G, compose
from l4_gen import lit, poly, Rcomp, R2, P7, Q13, Phi7, G7

def add(p, q):
    n = max(len(p), len(q)); r = [Fr(0)] * n
    for i, c in enumerate(p): r[i] += c
    for i, c in enumerate(q): r[i] += c
    return r
def scal(c, p): return [c * x for x in p]
def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] += a * b
    return r

E18 = [Fr(1, factorial(k)) for k in range(18)]
S17 = [c if k % 2 else Fr(0) for k, c in enumerate(E18)]
C16 = [c if k % 2 == 0 else Fr(0) for k, c in enumerate(E18)]
W = [Fr(0)] * 15; W[0] = Fr(1)
for k, c in enumerate(P7):
    if c: W[k + 1] += 2 * c * 2 ** k
br = add(pmul([Fr(0), Fr(1)], C16), scal(-1, pmul(S17, W)))
assert all(c == 0 for c in br[:17])
T = br[17:]
assert sum(abs(c) for c in T) <= Fr(24, 10 ** 9)
F7 = [g / 4 for g in G7]
# derivative of GPoly
GD = [k * c for k, c in enumerate(G7)][1:]  # coefficient of α^(k-1)

Rks = [k for k, c in enumerate(Rcomp) if c and k > 0]
R2ks = [k for k, c in enumerate(R2) if c and k > 0]

def haves(name, ks, indent="  "):
    return "\n".join(f"{indent}have {name}{k} := hp {k}" for k in ks)

out = open(sys.argv[1] if len(sys.argv) > 1 else '/dev/stdout', 'w')
out.write(open('l4_template.lean').read()
    .replace("@@E18@@", poly(E18, "x"))
    .replace("@@S17@@", poly(S17, "u"))
    .replace("@@C16@@", poly(C16, "u"))
    .replace("@@LPPOLY@@", poly(P7, "s"))
    .replace("@@WPOLY@@", poly(W, "u"))
    .replace("@@TPOLY@@", poly(T, "u"))
    .replace("@@IPPOLY@@", poly(Q13, "x"))
    .replace("@@RCOMP@@", poly(Rcomp, "x"))
    .replace("@@PHIPOLY@@", poly(Phi7, "A"))
    .replace("@@GPOLY@@", poly(G7, "α"))
    .replace("@@GDPOLY@@", poly(GD, "α"))
    .replace("@@FPOLY@@", poly(F7, "α"))
    .replace("@@R2@@", poly(R2, "A"))
    .replace("@@RCOMP_HAVES@@", haves("h", Rks))
    .replace("@@R2_HAVES@@", haves("h", R2ks))
    .replace("@@T_HAVES@@", haves("h", [k for k, c in enumerate(T) if c and k > 0]))
    .replace("@@W_HAVES@@", haves("h", [k for k, c in enumerate(W) if c and k > 0]))
    .replace("@@GD_HAVES@@", haves("h", [k for k, c in enumerate(GD) if c and k > 0]))
    .replace("@@PHI_HAVES@@", haves("h", [k for k, c in enumerate(Phi7) if c and k > 0]))
    .replace("@@Q_HAVES@@", haves("h", [k - 1 for k, c in enumerate(Q13) if c and k > 1]))
)
out.close()
