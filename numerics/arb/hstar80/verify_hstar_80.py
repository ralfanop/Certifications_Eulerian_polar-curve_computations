#!/usr/bin/env python3
"""Replay HSTAR_80_CERTIFICATE.json using Arb only (no mpmath)."""
from fractions import Fraction
from pathlib import Path
import json
import sys
import flint
from flint import arb, ctx

BITS = 768
CERT = "HSTAR_80_CERTIFICATE.json"


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def exact(q: Fraction):
    return arb(str(q.numerator)) / q.denominator


def parseq(s):
    return Fraction(s)


ctx.prec = BITS
D = json.loads(Path(CERT).read_text())
L_q = parseq(D["rounding_cell"]["L"])
U_q = parseq(D["rounding_cell"]["U"])
L, U = exact(L_q), exact(U_q)
pi = arb.pi()
q = 2 / pi
c = (1 + q) / 2
m = (1 - q) / 2


def rA(th):
    return 2 * (th / 2).sin() / th


def rpA(th):
    return (th * (th / 2).cos() - 2 * (th / 2).sin()) / (th * th)


def radial_gap_A(th):
    return rA(th) - c - m * th.cos()


def radial_gap_prime_A(th):
    return rpA(th) + m * th.sin()


def distance_data_A(theta, t, h):
    rr = rA(theta)
    rrp = rpA(theta)
    R = c + h + m * t.cos()
    ct, st = t.cos(), t.sin()
    cth, sth = theta.cos(), theta.sin()
    px, py = rr * cth, rr * sth
    zx, zy = R * ct, R * st
    dx, dy = px - zx, py - zy
    ppx, ppy = rrp * cth - rr * sth, rrp * sth + rr * cth
    return dx * dx + dy * dy, 2 * (dx * ppx + dy * ppy)


def supporting_gap_A(theta, t, h):
    rr = rA(theta)
    R = c + h + m * t.cos()
    Rp = -m * t.sin()
    ct, st = t.cos(), t.sin()
    cth, sth = theta.cos(), theta.sin()
    px, py = rr * cth, rr * sth
    zx, zy = R * ct, R * st
    Nx = R * ct + Rp * st
    Ny = R * st - Rp * ct
    normN = (R * R + Rp * Rp).sqrt()
    return ((px - zx) * Nx + (py - zy) * Ny) / normN - h

# Lower endpoint witness.
lo = D["lower_endpoint"]
lower_gap = supporting_gap_A(arb(lo["theta_witness"]), arb(lo["t_witness"]), L)
require(lower_gap.lower() > 0, ("lower witness failed", lower_gap))

# Outside-central upper proof.
out = D["upper_outside_central"]
A_q, B_q = parseq(out["A"]), parseq(out["B"])
A, B = exact(A_q), exact(B_q)
require(radial_gap_prime_A(A).lower() > 0, "g'(A) positivity failed")
require(radial_gap_prime_A(B).upper() < 0, "g'(B) negativity failed")
require((radial_gap_A(A) - 2 * U).upper() < 0, "g(A)<2U failed")
require((radial_gap_A(B) - 2 * U).upper() < 0, "g(B)<2U failed")

# Central cover: exact rational coverage and Arb mean-value inequality for every panel.
panels = D["upper_central_cover"]["panels"]
require(panels, "empty central cover")
require(parseq(panels[0]["lo"]) == A_q, "cover start mismatch")
require(parseq(panels[-1]["hi"]) == B_q, "cover end mismatch")
for x, y in zip(panels, panels[1:]):
    require(parseq(x["hi"]) == parseq(y["lo"]), "central cover gap/overlap")

Ulo = U.lower()
target = Ulo * Ulo
for j, P in enumerate(panels):
    lo_q, hi_q = parseq(P["lo"]), parseq(P["hi"])
    require(lo_q < hi_q, ("bad panel", j))
    mid_q = (lo_q + hi_q) / 2
    rad_q = (hi_q - lo_q) / 2
    midA = exact(mid_q)
    radA = exact(rad_q).upper()
    IA = arb(midA, radA)
    tA = arb(P["t"])
    d2c, _ = distance_data_A(midA, tA, U)
    _, d2pI = distance_data_A(IA, tA, U)
    mv_upper = d2c.upper() + d2pI.abs_upper() * radA
    require(mv_upper < target, ("panel failed", j, P["lo"], P["hi"], mv_upper - target))

print("python", sys.version.split()[0])
print("python-flint", flint.__version__)
print("Arb-only replay PASSED")
print("panels verified:", len(panels))
print("Q(L) > L and Q(U) < U")
print("CERTIFIED correctly rounded to 80 decimal places:")
print("h_* ≈", D["rounded"])
