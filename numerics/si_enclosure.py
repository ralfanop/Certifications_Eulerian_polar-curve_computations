"""Rigorous interval enclosures of the closed-form constants of the V478 manuscript and check of
the printed decimals against the paper's own criterion: the enclosure [L,U] must lie inside the
rounding cell of the printed decimal ("approx d").  A decimal printed as "d..." (truncated) is
certified when [L,U] lies inside [d, d + 10^-k).  Equation numbers are those of the V478 PDF.
All comparisons are exact (Python Fractions of the binary interval endpoints).

Interval arithmetic: mpmath.iv (outward-rounded).  Si(x) is evaluated from its power series
  Si(x) = sum_k (-1)^k x^(2k+1) / ((2k+1)(2k+1)!)
with an explicit alternating-series tail enclosure [-T, T], T = first omitted term, valid once
the terms decrease monotonically (checked below).
"""
import mpmath as mp
from mpmath import iv

iv.dps = 140
PI = iv.pi

def Si(x):
    # x: iv interval, positive, |x| < 6
    xu = mp.mpf(x.b)
    s = iv.mpf(0)
    term = x  # k = 0 term without the 1/(2k+1) factor: x^(2k+1)/(2k+1)!
    k = 0
    while True:
        s += (-1) ** k * term / (2 * k + 1)
        k += 1
        term = term * x * x / ((2 * k) * (2 * k + 1))
        # monotone decrease of |terms| from here on: ratio x^2/((2k+2)(2k+3)) * (2k+1)/(2k+3) < 1
        if (2 * k + 2) * (2 * k + 3) > xu * xu and mp.mpf((term / (2 * k + 1)).b) < mp.mpf(10) ** (-150):
            T = term / (2 * k + 1)
            return s + iv.mpf([-T.b, T.b])

S1 = Si(PI / 2)
S3 = Si(3 * PI / 2)
Sp = Si(PI)
A0 = 4 / PI * S1
bE = 2 / PI * S1
aE = 2 / PI * (S3 - S1)
err1 = bE - aE - 2 / PI
Etot = 4 / PI * Sp - 8 / PI**2
rms = iv.sqrt((Etot - A0**2 / 2 - aE**2) / 2)
rel = PI / 2 * err1 * 100
tab = [100 * A0**2 / (2 * Etot), 100 * (A0**2 + 2 * aE**2) / (2 * Etot), 100 * aE**2 / (Etot - A0**2 / 2)]
def arctan_small(y):
    # alternating series, 0 < y < 1/3, explicit tail bound
    s = iv.mpf(0); p = y; k = 0
    while mp.mpf(p.b) / (2 * k + 1) > mp.mpf(10) ** (-150):
        s += (-1) ** k * p / (2 * k + 1); p = p * y * y; k += 1
    T = p / (2 * k + 1)
    return s + iv.mpf([-T.b, T.b])
vdeg = 2 * arctan_small(1 / PI) * 180 / PI   # arccot(pi) = arctan(1/pi)

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
    # the 80-place value of V477 (now in the certificate only)
    ("b_E-a_E-2/pi, 80 places", err1,
     "0.08476693004920185826046136672445059341138112710639246276126231350179320866198109"),
]
truncated = [
    ("projection Hausdorff error (Sec. 3.10 discussion)", err1, "0.0847669"),
]

from fractions import Fraction as Fr
from mpmath import libmp

def ends(enc):
    return Fr(*libmp.to_rational(enc._mpi_[0])), Fr(*libmp.to_rational(enc._mpi_[1]))

def in_cell(enc, dec):
    d = Fr(dec)
    nd = len(dec.split(".")[1])
    half = Fr(1, 2 * 10 ** nd)
    lo, hi = ends(enc)
    return d - half < lo and hi < d + half, nd

def in_trunc(enc, dec):
    d = Fr(dec)
    nd = len(dec.split(".")[1])
    lo, hi = ends(enc)
    return d <= lo and hi < d + Fr(1, 10 ** nd), nd

mp.mp.dps = 140
print("Si(pi/2)  in", mp.nstr(mp.mpf(S1.a), 40), mp.nstr(mp.mpf(S1.b) - mp.mpf(S1.a), 3))
for name, enc, dec in paper:
    ok, nd = in_cell(enc, dec)
    width = mp.mpf(enc.b) - mp.mpf(enc.a)
    print(f"{name:34s} printed {nd:3d} dp  certified-in-cell={ok}  enclosure width={mp.nstr(width, 3)}")
for name, enc, dec in truncated:
    ok, nd = in_trunc(enc, dec)
    print(f"{name:34s} printed {dec}...  certified-truncation={ok}")
