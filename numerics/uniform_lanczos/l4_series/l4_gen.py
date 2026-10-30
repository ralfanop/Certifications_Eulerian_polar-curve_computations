#!/usr/bin/env python3
"""Generate Lean polynomial text for Task L4."""
from fractions import Fraction as Fr
from l4_series import Lp, Ip, phiA, G, compose, mul, W

def lit(c):
    """Lean real literal for a rational."""
    if c.denominator == 1:
        return f"({c.numerator} : ℝ)" if c.numerator >= 0 else f"(({c.numerator} : ℝ))"
    s = f"({c.numerator} / {c.denominator} : ℝ)"
    return s

def poly(coeffs, var, shift=0):
    """sum coeffs[k] * var^(k+shift) as Lean text (skip zeros)."""
    terms = []
    for k, c in enumerate(coeffs):
        if c == 0: continue
        e = k + shift
        mono = "" if e == 0 else (f" * {var}" if e == 1 else f" * {var} ^ {e}")
        terms.append(f"{lit(c)}{mono}")
    return " + ".join(terms) if terms else "(0 : ℝ)"

P7 = Lp[:14]
Q13 = Ip[:14]
comp = compose(P7, Q13, 169)
comp[1] -= 1
assert all(c == 0 for c in comp[:15])
Rcomp = comp[15:]  # polynomial in x, degrees 0..154 (even only)

Phi7 = phiA[:8]        # in A
G7 = G[:8]             # in alpha
comp2 = compose(Phi7, G7, 49)  # wait: we need G(Phi(A)) - A: G composed with Phi
comp2 = compose(G7, Phi7, 49)
comp2[1] -= 1
assert all(c == 0 for c in comp2[:8]), comp2[:8]
R2 = comp2[8:]

def bound(coeffs, b):
    return sum(abs(c) * b**k for k, c in enumerate(coeffs))

if __name__ == '__main__':
    import sys
    print("-- LpPoly"); print(poly(P7, "s"))
    print("-- IpPoly"); print(poly(Q13, "x"))
    print("-- Rcomp nonzero count", sum(1 for c in Rcomp if c))
    print("-- PhiPoly"); print(poly(Phi7, "A"))
    print("-- GPoly"); print(poly(G7, "α"))
    print("-- R2"); print(poly(R2, "A"))
    print("bound R at 1/40:", float(bound(Rcomp, Fr(1, 40))))
    print("bound R2 at A<=1/1600:", float(bound(R2, Fr(1, 1600))))
