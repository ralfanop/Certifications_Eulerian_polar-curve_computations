#!/usr/bin/env python3
"""Arb certification of the decimals printed in manuscript V001 (Eulerian polar curve) that are
not already covered by an Arb certificate.

Already covered by Arb certificates in this folder (replayed separately, see README.md):
  * h_* to 80 places (hstar80/HSTAR_80_CERTIFICATE.json), hence Eq. (70) to 20 places;
  * D_kappa, Eq. (50), and the two half-lengths (dkappa/D_K_CERTIFICATE_32_64.json).
This script certifies, in Arb ball arithmetic (python-flint), every other printed decimal of V001,
and re-derives from the two certificates above the decimals that depend on them (b_H, the 0.94 %
and 42 % gains, the curve lengths 5.5510... and 5.5243..., the margin 1.34e-80).

Criterion (V001, as in the rest of this repository): a decimal printed as "approx d" is certified
when the Arb enclosure lies strictly inside the rounding cell (d - 10^-k/2, d + 10^-k/2); a decimal
printed as "d..." is certified when the enclosure lies in [d, d + 10^-k).  Every comparison is a
certain Arb comparison between balls (an Arb comparison is true only if it holds for every point
of both balls), or an exact comparison of rationals.

Mathematical inputs (proved in V001, several formalised in Lean, lean/EulerianCert):
  Eq. (6)  A_0 = (4/pi) Si(pi/2);  Eqs (27)-(28)  b_E = A_0/2,  a_E = A_1 = (2/pi)(Si(3pi/2) - Si(pi/2));
  Eq. (29) ||r_E - r_L||_inf = b_E - a_E - 2/pi;  Eq. (33)  vartheta_E = 2 arccot pi;
  Sec. 3.7 E_tot = (4/pi) Si(pi) - 8/pi^2, Eqs (47)-(48) and Table 1;
  Thm 3.12 S(theta) = (2 sin(theta/2) - theta cos(theta/2))/(theta^2 sin theta) - m is strictly
           increasing on (0, pi) with unique zero theta_*; Delta = r_E(theta_*) - c - m cos theta_*,
           eps_rad = Delta/2, b_rad = c + eps_rad, with c = 1/2 + 1/pi, m = 1/2 - 1/pi;
  Thm 3.13 b_H = c + h_*, a_H = m;  Sec. 3.11 z_0 coth z_0 = (1/sqrt2) cot(1/sqrt2) (Lean);
  Remark 3.16 c_n = n! / ((n+1)(E(n,(n-1)/2) - E(n,(n-3)/2))) for odd n (exact integers).
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys
import time

import flint
from flint import arb, ctx

BITS = 768
ctx.prec = BITS
HERE = Path(__file__).resolve().parent
T0 = time.time()


def ex(q):
    """Arb ball containing the rational q (rounded outward by Arb)."""
    q = Q(q)
    return arb(str(q.numerator)) / q.denominator


def ball(lo, hi):
    """Arb ball containing the closed rational interval [lo, hi]."""
    lo, hi = Q(lo), Q(hi)
    B = arb(ex((lo + hi) / 2), ex((hi - lo) / 2).upper())
    assert B.lower() <= ex(lo).lower() and ex(hi).upper() <= B.upper()
    return B


def ndp(dec):
    return len(dec.split(".")[1])


def rounded_ok(x, dec):
    d, h = Q(dec), Q(1, 2 * 10 ** ndp(dec))
    return bool(x.lower() > ex(d - h).upper()) and bool(x.upper() < ex(d + h).lower())


def truncated_ok(x, dec):
    d, u = Q(dec), Q(1, 10 ** ndp(dec))
    return bool(x.lower() >= ex(d).upper()) and bool(x.upper() < ex(d + u).lower())


def rounded_ok_q(lo, hi, dec):
    d, h = Q(dec), Q(1, 2 * 10 ** ndp(dec))
    return d - h < lo and hi < d + h


def truncated_ok_q(lo, hi, dec):
    d, u = Q(dec), Q(1, 10 ** ndp(dec))
    return d <= lo and hi < d + u


ROWS = []        # (where, printed, kind, ok, enclosure)
NEGATIVE = []    # (description, ok) -- must all be False


def check(where, printed, x, kind="approx"):
    ok = rounded_ok(x, printed) if kind == "approx" else truncated_ok(x, printed)
    ROWS.append((where, printed + ("..." if kind == "trunc" else ""), kind, ok, x.str(40)))


def check_q(where, printed, lo, hi, kind="approx", enclosure=""):
    ok = rounded_ok_q(lo, hi, printed) if kind == "approx" else truncated_ok_q(lo, hi, printed)
    ROWS.append((where, printed + ("..." if kind == "trunc" else ""), kind, ok, enclosure))


def negative(desc, ok):
    NEGATIVE.append((desc, ok))


# ------------------------------------------------------------------ constants of Prop. 3.1, Sec. 3.7
pi = arb.pi()
S1, S3, Sp = (pi / 2).si(), (3 * pi / 2).si(), pi.si()
A0 = 4 / pi * S1
bE = 2 / pi * S1
aE = 2 / pi * (S3 - S1)
err1 = bE - aE - 2 / pi
Etot = 4 / pi * Sp - 8 / (pi * pi)
rms = ((Etot - A0 * A0 / 2 - aE * aE) / 2).sqrt()
rel = pi / 2 * err1 * 100
tab = [100 * A0 * A0 / (2 * Etot),
       100 * (A0 * A0 + 2 * aE * aE) / (2 * Etot),
       100 * aE * aE / (Etot - A0 * A0 / 2)]
vartheta_deg = 2 * (1 / pi).atan() * 180 / pi

check("Eq. (6) A_0", "1.745308598921205431531889", A0)
check("Eq. (27) b_E", "0.872654299460602715765944", bE)
check("Eq. (28) a_E", "0.151267597043819514429948", aE)
check("Eq. (29) b_E - a_E - 2/pi (also Sec. 3.10)", "0.08476693004920185826", err1)
check("Eq. (33) vartheta_E in degrees", "35.3135743", vartheta_deg)
check("Eq. (47) RMS residual", "0.026991490844990871037657", rms)
check("Eq. (48) relative endpoint error, %", "13.315158235496622430663396", rel)
check("Table 1, row 1, %", "98.427", tab[0])
check("Table 1, row 2, %", "99.906", tab[1])
check("Table 1, row 3, %", "94.013", tab[2])
check("Sec. 4, projection Hausdorff error", "0.0847669", err1, kind="trunc")
negative("Eq. (29) with last digit lowered (…825)", rounded_ok(err1, "0.08476693004920185825"))
negative("Table 1 row 1 as 98.426", rounded_ok(tab[0], "98.426"))

# ------------------------------------------------------------------ Theorem 3.12 (radial minimax)
c = 1 / ex(2) + 1 / pi
m = 1 / ex(2) - 1 / pi


def S(th):
    return (2 * (th / 2).sin() - th * (th / 2).cos()) / (th * th * th.sin()) - m


lo, hi = Q(2), Q(11, 5)
assert S(ex(lo)).upper() < 0 and S(ex(hi)).lower() > 0, "initial bracket for theta_*"
while hi - lo > Q(1, 10 ** 80):
    mid = (lo + hi) / 2
    v = S(ex(mid))
    if v.upper() < 0:
        lo = mid
    elif v.lower() > 0:
        hi = mid
    else:
        break
# S(lo) < 0 < S(hi) certified at every step; S strictly increasing (Thm 3.12): theta_* in (lo, hi)
assert S(ex(lo)).upper() < 0 and S(ex(hi)).lower() > 0
TH = ball(lo, hi)
Delta = 2 * (TH / 2).sin() / TH - c - m * TH.cos()
eps = Delta / 2
brad = c + eps
check_q("Eq. (59) theta_*", "2.10258309466509376393", lo, hi,
        enclosure=f"({float(lo):.20f}, {float(hi):.20f}), width {float(hi - lo):.1e}")
check("Eq. (60) Delta", "0.09953351643838914835807", Delta)
check("Eq. (60) eps_rad", "0.04976675821919457417904", eps)
check("Eq. (61) b_rad = c + eps_rad", "0.86807664440298524572", brad)
check("Abstract, Sec. 1: eps_rad", "0.0497668", eps)
negative("eps_rad truncated (…17903, earlier draft)", rounded_ok(eps, "0.04976675821919457417903"))
negative("eps_rad approx 0.0497667 (truncation)", rounded_ok(eps, "0.0497667"))

# ------------------------------------------------------------------ Theorem 3.13 (from the h_* Arb certificate)
H = json.loads((HERE / "hstar80" / "HSTAR_80_CERTIFICATE.json").read_text())
HL, HU = Q(H["rounding_cell"]["L"]), Q(H["rounding_cell"]["U"])   # L < h_* < U (Arb certificate)
assert HU - HL == Q(1, 10 ** 80)
hs = ball(HL, HU)
bH = c + hs
check_q("Eq. (70) h_* (from the 80-place Arb certificate)", "0.04929794832571833571", HL, HU,
        enclosure="80-place cell of " + H["rounded"][:30] + "...")
check_q("Abstract, Sec. 1: h_*", "0.0492979", HL, HU, enclosure="(same)")
check("Eq. (71) b_H = c + h_*", "0.86760783450950900724", bH)
ok72a = bool(ex(HU).upper() < eps.lower()) and HL > 0
ok72b = bool((c + ex(HL)).lower() > (2 * m).upper()) and bool(m.lower() > 0)
gain_rad = 100 * (1 - hs / eps)
gain_proj = 100 * (1 - hs / err1)
check("Secs 1, 3.12, 4: gain 1 - h_*/eps_rad, %", "0.94", gain_rad)
about42 = bool(gain_proj.lower() > ex(Q(83, 2)).upper()) and bool(gain_proj.upper() < ex(Q(85, 2)).lower())


# margin of the lower witness (Sec. 3.10: "the certified margin exceeds 1.34e-80")
def supporting_gap(theta, t, h):
    rr = 2 * (theta / 2).sin() / theta
    R = c + h + m * t.cos()
    Rp = -m * t.sin()
    ct, st, cth, sth = t.cos(), t.sin(), theta.cos(), theta.sin()
    px, py, zx, zy = rr * cth, rr * sth, R * ct, R * st
    Nx, Ny = R * ct + Rp * st, R * st - Rp * ct
    return ((px - zx) * Nx + (py - zy) * Ny) / (R * R + Rp * Rp).sqrt() - h


lw = H["lower_endpoint"]
gapL = supporting_gap(arb(lw["theta_witness"]), arb(lw["t_witness"]), ex(HL))
ok134 = bool(gapL.lower() > ex(Q(134, 10 ** 82)).upper())

# ------------------------------------------------------------------ Sec. 3.11, Montgomery-Taylor
x = 1 / ex(2).sqrt()
zcoth = x * x.cos() / x.sin()          # z_0 coth z_0 = (1/sqrt2) cot(1/sqrt2)
check("Sec. 3.11 C_MT = 1/2 + z_0 coth z_0", "1.3274992963", 1 / ex(2) + zcoth, kind="trunc")
check("Sec. 3.11 3/2 - z_0 coth z_0", "0.6725007", ex(Q(3, 2)) - zcoth, kind="trunc")

# ------------------------------------------------------------------ Remark 3.16 (exact integers, then Arb)
def central_c(nmax, wanted):
    row, fact, out = [1], 1, {}
    for n in range(2, nmax + 1):
        fact *= n
        new = [0] * n
        for k in range(1, n + 1):
            a = k * row[k - 1] if k - 1 < len(row) else 0
            b = (n - k + 1) * row[k - 2] if k >= 2 else 0
            new[k - 1] = a + b
        row = new
        if n in wanted:
            assert sum(row) == fact and row == row[::-1]
            kc = (n + 1) // 2
            out[n] = Q(fact, (n + 1) * (row[kc - 1] - row[kc - 2]))
    return out


C = central_c(671, (669, 671))
c669, c671 = ex(C[669]), ex(C[671])
check("Eq. (93) c_669", "3.13914926973", c669, kind="trunc")
check("Eq. (93) c_671", "3.14377888960", c671, kind="trunc")
ok93 = (C[669] < Q(333, 106) and Q(355, 113) < C[671]
        and bool(pi.lower() > ex(Q(333, 106)).upper()) and bool(pi.upper() < ex(Q(355, 113)).lower()))
cross = 216 * pi - ex(Q(15, 2))
okcross = bool(cross.lower() > 670) and bool(cross.upper() < 672)

# ------------------------------------------------------------------ from the D_kappa Arb certificate
DK = json.loads((HERE / "dkappa" / "D_K_CERTIFICATE_32_64.json").read_text())
def stored(obj):
    # 60-digit bounds rounded outward from the Arb balls (rational_bounds in dkappa/certify_dk.py)
    return Q(obj["lower"]), Q(obj["upper"])
LEl, LEu = stored(DK["half_lengths"]["E"])
LLl, LLu = stored(DK["half_lengths"]["L"])
Dl, Du = stored(DK["D"])
check_q("Eq. (50) D_kappa (from the D_kappa Arb certificate)", "0.203783759536049443826081", Dl, Du,
        enclosure=f"[{DK['D']['lower'][:32]}, {DK['D']['upper'][:32]}]")
check_q("after Eq. (50): Eulerian curve length 2 L_E", "5.5510", 2 * LEl, 2 * LEu, kind="trunc",
        enclosure=f"2 x [{DK['half_lengths']['E']['lower'][:24]}, ...]")
check_q("after Eq. (50): limacon length 2 L_L", "5.5243", 2 * LLl, 2 * LLu, kind="trunc",
        enclosure=f"2 x [{DK['half_lengths']['L']['lower'][:24]}, ...]")

# ------------------------------------------------------------------ report
print("V001 decimals certified in Arb ball arithmetic")
print(f"python {sys.version.split()[0]}; python-flint {flint.__version__}; precision {BITS} bits")
print(f"script sha256 {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}")
print()
width = max(len(r[0]) for r in ROWS)
for where, printed, kind, ok, enc in ROWS:
    print(f"{where:{width}s}  {printed:30s}  {'CERTIFIED' if ok else 'FAIL'}")
    if enc:
        print(f"{'':{width}s}    enclosure {enc}")
print()
claims = [
    ("Eq. (72) 0 < h_* < eps_rad", ok72a),
    ("Eq. (72) b_H > 2 a_H > 0, a_H = m", ok72b),
    ("Sec. 4: 1 - h_*/(b_E - a_E - 2/pi) is about 42 % (in [41.5, 42.5) %)", about42),
    ("Sec. 3.13 proof: lower-witness margin exceeds 1.34e-80", ok134),
    ("Eq. (93): c_669 < 333/106 < pi < 355/113 < c_671", ok93),
    ("Remark 3.16: 670 < 216 pi - 15/2 < 672", okcross),
]
for desc, ok in claims:
    print(f"{desc:{width + 32}s}  {'CERTIFIED' if ok else 'FAIL'}")
print(f"{'':{width}s}    gain over the radial optimum  {gain_rad.str(12)} %")
print(f"{'':{width}s}    gain over the projection      {gain_proj.str(12)} %")
print(f"{'':{width}s}    lower-witness margin          {gapL.str(12)}")
print(f"{'':{width}s}    216 pi - 15/2                 {cross.str(12)}")
print()
for desc, ok in NEGATIVE:
    print(f"negative control: {desc:58s} {'(passes: ERROR)' if ok else 'rejected, as it must be'}")
print()
allok = all(r[3] for r in ROWS) and all(ok for _, ok in claims) and not any(ok for _, ok in NEGATIVE)
print(f"{len(ROWS)} printed decimals, {len(claims)} inequalities, {len(NEGATIVE)} negative controls")
print("ALL CERTIFIED" if allok else "SOME CHECK FAILED")
print(f"elapsed {time.time() - T0:.1f}s")
sys.exit(0 if allok else 1)
