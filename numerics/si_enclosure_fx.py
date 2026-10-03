"""Independent replay of si_enclosure.py with ia_fixed (exact-integer fixed-point intervals, no
mpmath, no floating point).  Same closed forms, same printed decimals, same exact criterion:
the enclosure [L,U] must lie inside the rounding cell of the printed decimal (or, for a value
printed as "d...", inside [d, d + 10^-k)).  Equation numbers are those of the V478 PDF.

Si(x) = sum_k (-1)^k x^(2k+1) / ((2k+1)(2k+1)!): alternating series; once the terms decrease
monotonically the tail is enclosed by [-T, T], T = first omitted term (monotonicity is checked).
arctan(y), 0 < y < 1: alternating series with the same tail bound.
"""
from fractions import Fraction as Fr
import time
import ia_fixed as F

t0 = time.time()
PI = F.PI
FI = F.FI

def Si(x):
    assert x.lo > 0
    xh = Fr(x.hi, 1 << F.P)
    x2 = x * x
    s = FI(0)
    term = x           # x^(2k+1)/(2k+1)!
    k = 0
    while True:
        t = term / (2 * k + 1)
        s = s + t if k % 2 == 0 else s - t
        k += 1
        term = term * x2 / ((2 * k) * (2 * k + 1))
        T = term / (2 * k + 1)          # first omitted term (k-th)
        # terms decrease from index k on: ratio x^2 (2j+1) / ((2j+2)(2j+3)^2) < 1 for j >= k
        mono = xh * xh * (2 * k + 1) < (2 * k + 2) * (2 * k + 3) ** 2
        if mono and T.abs().hi < 16:
            b = T.abs().hi + 1
            return s + FI(-b, b)

def arctan_small(y):
    yh = Fr(y.hi, 1 << F.P)
    assert y.lo > 0 and yh < 1
    y2 = y * y
    s, p, k = FI(0), y, 0
    while True:
        t = p / (2 * k + 1)
        s = s + t if k % 2 == 0 else s - t
        k += 1
        p = p * y2
        T = p / (2 * k + 1)
        if T.abs().hi < 16:
            b = T.abs().hi + 1
            return s + FI(-b, b)

S1 = Si(PI / 2)
S3 = Si(3 * PI / 2)
Sp = Si(PI)
A0 = 4 / PI * S1
bE = 2 / PI * S1
aE = 2 / PI * (S3 - S1)
err1 = bE - aE - 2 / PI
Etot = 4 / PI * Sp - 8 / (PI * PI)
rms = F.sqrt((Etot - A0 * A0 / 2 - aE * aE) / 2)
rel = PI / 2 * err1 * 100
tab = [100 * A0 * A0 / (2 * Etot), 100 * (A0 * A0 + 2 * aE * aE) / (2 * Etot),
       100 * aE * aE / (Etot - A0 * A0 / 2)]
vdeg = 2 * arctan_small(1 / PI) * 180 / PI

paper = [
    ("A0 (Eq. 6)", A0, "1.745308598921205431531889"),
    ("b_E (Eq. 27)", bE, "0.872654299460602715765944"),
    ("a_E (Eq. 28)", aE, "0.151267597043819514429948"),
    ("b_E-a_E-2/pi (Eq. 29, Cor. 3.9)", err1, "0.08476693004920185826"),
    ("rms (Eq. 47)", rms, "0.026991490844990871037657"),
    ("relative endpoint % (Eq. 48)", rel, "13.315158235496622430663396"),
    ("Table 1 row 1 %", tab[0], "98.427"),
    ("Table 1 row 2 %", tab[1], "99.906"),
    ("Table 1 row 3 %", tab[2], "94.013"),
    ("vartheta_E degrees (Eq. 33)", vdeg, "35.3135743"),
    ("b_E-a_E-2/pi, 80 places", err1,
     "0.08476693004920185826046136672445059341138112710639246276126231350179320866198109"),
]
truncated = [
    ("projection Hausdorff error (Sec. 3.10 discussion)", err1, "0.0847669"),
]

def in_cell(enc, dec):
    d = Fr(dec); nd = len(dec.split(".")[1]); half = Fr(1, 2 * 10 ** nd)
    lo, hi = enc.to_fraction_bounds()
    return d - half < lo and hi < d + half, nd

def in_trunc(enc, dec):
    d = Fr(dec); nd = len(dec.split(".")[1])
    lo, hi = enc.to_fraction_bounds()
    return d <= lo and hi < d + Fr(1, 10 ** nd), nd

print(f"backend: ia_fixed, {F.P}-bit fixed point")
for name, enc, dec in paper:
    ok, nd = in_cell(enc, dec)
    lo, hi = enc.to_fraction_bounds()
    print(f"{name:34s} printed {nd:3d} dp  certified-in-cell={ok}  enclosure width={float(hi - lo):.2e}")
for name, enc, dec in truncated:
    ok, nd = in_trunc(enc, dec)
    print(f"{name:34s} printed {dec}...  certified-truncation={ok}")
print(f"elapsed {time.time() - t0:.1f}s")
