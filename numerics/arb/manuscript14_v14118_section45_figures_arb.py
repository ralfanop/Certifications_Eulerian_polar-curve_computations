#!/usr/bin/env python3
"""Manuscript 14, version 14.118 (8 November 2026): Section 4.5 with its Table 1, the paragraph of
Figure 2, the caption and the frame of Figure 1, and the plotted data of Figures 1-3.

Exact rational arithmetic and Arb balls at 2000 bits (python-flint 0.9.0). L(x) = coth x - 1/x is the
Langevin function and m(H) = 1/2 + L(H/2)/2 the magnetisation curve (44); H_0 = -1/sqrt2, H_1 = 2 H_0,
a = 1/sqrt8 = |H_0|/2, b = 1/sqrt2 = |H_1|/2.

  (A) Section 4.5, the values in the text. With k_B = 1.380649e-23 J/K, mu_B = 9.274e-24 J/T and
      |B| = |H| k_B T/(2 mu_p): for the oxygen molecule (mu_p = 2.64e-23 J/T, T = 293 K) mu_p = 2.85 mu_B,
      x = mu_p B/(k_B T) = 0.0065 at B = 1 T, H_0 and H_1 at about 54 T and 108 T and the window of
      Figure 1(b), whose largest field is |H| = 5/2 + 1/sqrt2, at about 246 T; for the cobalt particle
      (mu_p = 3e4 mu_B, T = 300 K) H_0 and H_1 at about 5.3 mT and 10.5 mT and the whole curve of
      Figure 1(a), up to |H| = 10, below 0.075 T; ln(tau_N/tau_at) = ln(100 s x 1e9 /s) is 25.
  (B) Table 1: for H = -1/sqrt2, -sqrt2, -2, -6.5 the printed x = H/2, L(x) and m(H) and the inductions
      |B| for O2 and Co (three significant digits) are correctly rounded.
  (C) Figure 1, caption and frame, and the last sentence of the paragraph of Figure 2:
      m(H) = 1 + 1/(e^H - 1) - 1/H and m(-H) = 1 - m(H) at sample points; the saturation values
      approached as 1/|H| (H(1 - m(H)) = |H| m(-H) = 1 - H/(e^H - 1), 0 < H/(e^H - 1) < 2H e^-H, at
      H = 10, 20, 50, 100; the general statement is the Lean module V14118Section45Certificate); the only
      inflection point at H = 0: L''(x) < 0 for every x > 0 (exact Bernoulli bound on (0, 1/2], Arb
      bisection on [1/2, 5], exact exponential bound on [5, oo)) and L'' is odd, so m''(H) = L''(H/2)/8
      is positive for H < 0 and negative for H > 0; at H_0 the curve is convex with second derivative
      m''(H_0) = L''(-a)/8 = -L''(a)/8 > 0; m(0) = 1/2 and slope m'(0) = L'(0)/4 = 1/12 (the drawn
      tangent from (-5.2, 0.06666667) to (5.2, 0.93333333)); the window of panel (b) centred at H_0; the
      rectangle of panel (a) = frame of panel (b), the guides and the markers, [H_0 -+ 2.5] x
      [m(H_0) -+ 0.1375], H_0, H_1, m(H_0), m(H_1) to the printed twelve decimals of the figure source;
      the labels m(H_0) = 0.4416, m(H_1) = 0.3859.
  (D) Figure 1, plotted data: every point of fig01_langevin_S.dat (panel a) and fig01_langevin_zoom.dat
      (panel b) lies on m(H) within the stated tolerance; the zoom data start and end on the bottom and
      top edges of the frame of panel (b); fig01_points.dat.
  (E) Figure 2 and its paragraph: from the exact Eulerian numbers E(n, k), every printed centre and
      (n+1) x variance of fig02_centres.dat correctly rounded (n = 3, ..., 670; u = 1, e^{H_0}, e^{2H_0}); for n >= 10 the
      centres round to m(H_0) = 0.44156, m(H_1) = 0.38590 and the widths to Var_a/4 = L'(a)/4 = 0.08129,
      Var_b/4 = L'(b)/4 = 0.07562, as printed; the probabilities p_{n,k}(u) never exceed 2/3, attained
      only at the top vertex p_{3,2}(1) = 2/3; the dashed and dotted lines at m(H_0), m(H_1) and 1/2.
  (F) Figure 3: the Parry roots beta_31 > beta_32 (roots in (1, 2) of x^n - x^(n-1) - 1, n = 31, 32)
      isolated by exact rational sign changes; every plotted remainder T_beta^k(1),
      beta = beta_32 + h (beta_31 - beta_32), of fig06_orbit_k*.dat within 1e-12 of its Arb value, every
      floor decided by the ball; h_E = 0.9961 and T^31_{beta_E}(1) of beta_E = sqrt2 sinh(1/sqrt2); at
      beta_31 the thirtieth remainder is 1/beta_31 and T^31(1) = 0, with left limit 1.
  (G) The display of Tr(2/(2A+I)) = coth(b)/sqrt2 - 1, printed to 52 decimals in version 14.118.
"""
from fractions import Fraction as Q
import os
import sys
import flint
from flint import arb, fmpz, ctx

PREC = 2000
ctx.prec = PREC
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "manuscript14")
failures = []
count = 0


def check(desc, cond):
    global count
    ok = bool(cond)
    count += 1
    print(f"{'PASS' if ok else 'FAIL'} {count:03d}: {desc}")
    if not ok:
        failures.append(desc)


def qball(q):
    q = Q(q)
    return arb(fmpz(q.numerator)) / arb(fmpz(q.denominator))


def rounded(name, x, printed):
    """x lies strictly inside the rounding interval of the printed decimal."""
    center = Q(printed)
    places = len(printed.partition('.')[2]) if '.' in printed else 0
    half = Q(1, 2 * 10 ** places)
    check(f"{name} = {printed}, correctly rounded",
          x > qball(center - half) and x < qball(center + half))


def read(fname):
    rows = []
    with open(os.path.join(ROOT, fname)) as f:
        f.readline()
        for line in f:
            if line.strip():
                rows.append(line.split())
    return rows


def fl(x):
    """Midpoint of a ball as a float, for the log only."""
    return float(x.mid().str(15, radius=False))


def L(x):
    """Langevin function coth x - 1/x (x != 0)."""
    return x.coth() - 1 / x


def L1(x):
    """L'(x) = 1/x^2 - 1/sinh^2 x (x != 0)."""
    return 1 / x ** 2 - 1 / x.sinh() ** 2


def L2(x):
    """L''(x) = -2/x^3 + 2 cosh x / sinh^3 x (x != 0)."""
    return -2 / x ** 3 + 2 * x.cosh() / x.sinh() ** 3


def m(H):
    if H == 0:
        return qball(Q(1, 2))
    return arb(1) / 2 + L(H / 2) / 2


SQRT2 = arb(2).sqrt()
H0 = -1 / SQRT2
H1 = 2 * H0
a = 1 / arb(8).sqrt()
b = 1 / SQRT2
TINY = arb(2) ** (-1900)
print(f"Python {sys.version.split()[0]}, python-flint {flint.__version__}, Arb precision {ctx.prec} bits")

# ---------------------------------------------------------------------------------------------------
print("(A) Section 4.5")
kB = qball(Q("1.380649e-23"))
muB = qball(Q("9.274e-24"))
mu_O2 = qball(Q("2.64e-23"))
mu_Co = 30000 * muB
T_O2, T_Co = arb(293), arb(300)
f_O2 = kB * T_O2 / (2 * mu_O2)          # tesla per unit |H|
f_Co = kB * T_Co / (2 * mu_Co)
print(f"    O2: {f_O2.str(10, radius=False)} T per unit |H|;  Co: {f_Co.str(10, radius=False)} T per unit |H|")
rounded("(A) mu_p(O2)/mu_B", mu_O2 / muB, "2.85")
rounded("(A) x = mu_p B/(k_B T) for O2 at B = 1 T, 293 K", mu_O2 / (kB * T_O2), "0.0065")
rounded("(A) O2, |B| at H_0 in tesla, 'about 54 T'", f_O2 / SQRT2, "54")
rounded("(A) O2, |B| at H_1 in tesla, 'about 108 T'", f_O2 * SQRT2, "108")
Hwin = qball(Q(5, 2)) + 1 / SQRT2
rounded("(A) largest |H| of the window of Figure 1(b), 5/2 + 1/sqrt2", Hwin, "3.2071")
rounded("(A) O2, |B| at the edge of the window of Figure 1(b) in tesla, 'about 246 T'", f_O2 * Hwin, "246")
rounded("(A) Co, |B| at H_0 in millitesla, 'about 5.3 mT'", 1000 * f_Co / SQRT2, "5.3")
rounded("(A) Co, |B| at H_1 in millitesla, 'about 10.5 mT'", 1000 * f_Co * SQRT2, "10.5")
B10 = 10 * f_Co
print(f"    Co, |B| at |H| = 10: {B10.str(8, radius=False)} T")
check("(A) Co, the whole curve of Figure 1(a), up to |H| = 10, below 0.075 T", B10 < qball(Q("0.075")))
rounded("(A) blocking factor ln(tau_N/tau_at) = ln(100 x 1e9)", (arb(10) ** 11).log(), "25")

# ---------------------------------------------------------------------------------------------------
print("(B) Table 1")
table = [
    ("-1/sqrt2 = H_0", H0, "-0.3536", "-0.1169", "0.4416", "54.2", "0.00526"),
    ("-sqrt2 = H_1", H1, "-0.7071", "-0.2282", "0.3859", "108", "0.0105"),
    ("-2", arb(-2), "-1", "-0.3130", "0.3435", "153", "0.0149"),
    ("-6.5", qball(Q("-6.5")), "-3.25", "-0.6953", "0.1523", "498", "0.0484"),
]
for name, H, px, pL, pm, pB2, pBCo in table:
    x = H / 2
    rounded(f"(B) Table 1, H = {name}: x = H/2", x, px)
    rounded(f"(B) Table 1, H = {name}: L(x)", L(x), pL)
    rounded(f"(B) Table 1, H = {name}: m(H)", m(H), pm)
    rounded(f"(B) Table 1, H = {name}: |B| O2 293 K (T), three significant digits", f_O2 * abs(H), pB2)
    rounded(f"(B) Table 1, H = {name}: |B| Co 300 K (T), three significant digits", f_Co * abs(H), pBCo)

# ---------------------------------------------------------------------------------------------------
print("(C) Figure 1: caption and frame; the inflection point and the convexity at H_0")
for Hq in (Q(1, 2), Q(1), Q(2), Q(5), Q(10), Q(-3), Q(-10), Q(20)):
    H = qball(Hq)
    exact = 1 + 1 / (H.exp() - 1) - 1 / H
    check(f"(C) m(H) = 1 + 1/(e^H - 1) - 1/H at H = {Hq}", abs(m(H) - exact) < TINY)
    check(f"(C) m(-H) = 1 - m(H) at H = {Hq}", abs(m(-H) - (1 - m(H))) < TINY)
for Hq in (10, 20, 50, 100):
    H = arb(Hq)
    rem = H / (H.exp() - 1)
    check(f"(C) H (1 - m(H)) = 1 - H/(e^H - 1) at H = {Hq}", abs(H * (1 - m(H)) - (1 - rem)) < TINY)
    check(f"(C) |H| m(H) = 1 - H/(e^H - 1) at H = -{Hq}", abs(H * m(-H) - (1 - rem)) < TINY)
    check(f"(C) 0 < H/(e^H - 1) < 2 H e^-H at H = {Hq} (approach to saturation as 1/|H|)",
          rem > 0 and rem < 2 * H * (-H).exp())
    print(f"    H = {Hq}: 1 - H (1 - m(H)) = {rem.str(6, radius=False)}")
# (0, 1/2]: L''(x) = sum_{k>=2} a_k (2k-1)(2k-2) x^(2k-3) with a_k = 2^(2k) B_(2k)/(2k)!, a_2 = -1/45,
# a_3 = 2/945 and |a_k| = 2 zeta(2k)/pi^(2k) <= 4/9^k (pi^2 > 9), so for 0 < x <= 1/2
# L''(x)/x <= -2/15 + (8/189)/4 + sum_{k>=4} 256 k^2 36^(-k), and k^2 <= 2^k for k >= 4.
tail = Q(256) * Q(1, 18 ** 4) / (1 - Q(1, 18))
bound = Q(-2, 15) + Q(8, 189) / 4 + tail
check("(C) Bernoulli coefficients a_2 = 2^4 B_4/4! = -1/45 and a_3 = 2^6 B_6/6! = 2/945",
      Q(16) * Q(-1, 30) / 24 == Q(-1, 45) and Q(64) * Q(1, 42) / 720 == Q(2, 945))
check(f"(C) L''(x)/x <= {float(bound):.5f} < 0 for 0 < x <= 1/2 (exact rational bound)", bound < 0)
saved = ctx.prec
ctx.prec = 128                                                 # the bisection is rigorous at any precision
stack, pieces, ok_mid = [(Q(1, 2), Q(5))], 0, True
while stack:
    lo, hi = stack.pop()
    ball = arb(qball((lo + hi) / 2), qball((hi - lo) / 2))
    if L2(ball) < 0:
        pieces += 1
    elif hi - lo < Q(1, 10 ** 9):
        ok_mid = False
        break
    else:
        mid = (lo + hi) / 2
        stack += [(lo, mid), (mid, hi)]
ctx.prec = saved
check(f"(C) L''(x) < 0 on [1/2, 5], certified on {pieces} Arb interval balls", ok_mid)
# [5, oo): 2 cosh x/sinh^3 x <= 8 K e^(-2x), K = (1 + e^-10)/(1 - e^-10)^3, and 8 K e^(-2x) < 2/x^3
# because e^(2x)/x^3 is increasing for x > 3/2 and exceeds 4K at x = 5.
e10 = arb(-10).exp()
K = (1 + e10) / (1 - e10) ** 3
check("(C) L''(x) < 0 on [5, oo): e^10/125 > 4 (1 + e^-10)/(1 - e^-10)^3", arb(10).exp() / 125 > 4 * K)
check("(C) L'' is odd: L''(-x) = -L''(x) at x = 1/3, 1, 3",
      all(abs(L2(-qball(q)) + L2(qball(q))) < TINY for q in (Q(1, 3), Q(1), Q(3))))
mpp0 = L2(H0 / 2) / 8
print(f"    L''(a) = {L2(a).str(15, radius=False)};  m''(H_0) = L''(H_0/2)/8 = {mpp0.str(15, radius=False)}")
check("(C) at H_0 the curve is convex: m''(H_0) = L''(-a)/8 = -L''(a)/8 > 0",
      mpp0 > 0 and abs(mpp0 + L2(a) / 8) < TINY)
check("(C) slope at H_0: m'(H_0) = L'(-a)/4 = L'(a)/4 = Var_a(omega_3)/4", abs(L1(H0 / 2) / 4 - L1(a) / 4) < TINY)
check("(C) m(0) = 1/2 by continuity: |m(2^-300) - 1/2| < 2^-302", abs(m(arb(2) ** (-300)) - qball(Q(1, 2))) < arb(2) ** (-302))
h = arb(2) ** (-300)
check("(C) slope m'(0) = L'(0)/4 = 1/12: (m(h) - m(-h))/(2h) within 2^-500 of 1/12 at h = 2^-300",
      abs((m(h) - m(-h)) / (2 * h) - qball(Q(1, 12))) < arb(2) ** (-500))
rounded("(C) tangent m = 1/2 + H/12 at H = -5.2", qball(Q(1, 2) - Q("5.2") / 12), "0.06666667")
rounded("(C) tangent m = 1/2 + H/12 at H = 5.2", qball(Q(1, 2) + Q("5.2") / 12), "0.93333333")
check("(C) the window -2.5 - 1/sqrt2 <= H <= 2.5 - 1/sqrt2 of panel (b) is centred at H_0 = -1/sqrt2",
      abs(((-qball(Q(5, 2)) - 1 / SQRT2) + (qball(Q(5, 2)) - 1 / SQRT2)) / 2 - H0) < TINY)
m0, m1 = m(H0), m(H1)
rounded("(C) H_0", H0, "-0.707106781187")
rounded("(C) H_1", H1, "-1.414213562373")
rounded("(C) m(H_0)", m0, "0.441559707648")
rounded("(C) m(H_1)", m1, "0.385899079161")
rounded("(C) left edge H_0 - 2.5", H0 - qball(Q(5, 2)), "-3.207106781187")
rounded("(C) right edge H_0 + 2.5", H0 + qball(Q(5, 2)), "1.792893218813")
rounded("(C) bottom edge m(H_0) - 0.1375", m0 - qball(Q("0.1375")), "0.304059707648")
rounded("(C) top edge m(H_0) + 0.1375", m0 + qball(Q("0.1375")), "0.579059707648")
rounded("(C) label m(H_0)", m0, "0.4416")
rounded("(C) label m(H_1)", m1, "0.3859")
src1 = open(os.path.join(ROOT, "Remark_4.3_Langevin_Magnetisation_Curve.tex")).read()
for needle in ("(axis cs:-3.207106781187,0.304059707648) rectangle (axis cs:1.792893218813,0.579059707648)",
               "xmin=-3.207106781187,xmax=1.792893218813,ymin=0.304059707648,ymax=0.579059707648",
               "(-0.707106781187,0.304059707648) (-0.707106781187,0.441559707648) (-3.207106781187,0.441559707648)",
               "(-1.414213562373,0.304059707648) (-1.414213562373,0.385899079161) (-3.207106781187,0.385899079161)",
               "coordinates {(-0.707106781187,0.441559707648)}", "coordinates {(-1.414213562373,0.385899079161)}",
               "$m(H_0)=0.4416$", "$m(H_1)=0.3859$", "coordinates {(-5.2,0.06666667) (5.2,0.93333333)}",
               "coordinates {(0,0.5)}", "xmin=-10,xmax=10", "restrict x to domain=-10:10"):
    check(f"(C) Figure 1 source draws {needle}", needle in src1)

# ---------------------------------------------------------------------------------------------------
print("(D) Figure 1: plotted data")


def curve_data(fname, tol):
    rows = read(fname)
    ok, worst = True, 0.0
    for Hs, ms in rows:
        d = abs(m(qball(Q(Hs))) - qball(Q(ms)))
        if not d < qball(tol):
            ok = False
            print(f"    point ({Hs}, {ms}) off the curve: {d.str(5)}")
        worst = max(worst, fl(d))
    check(f"(D) {fname}: all {len(rows)} points lie on m(H) within {float(tol):.3e}", ok)
    print(f"    {fname}: largest deviation {worst:.3e}")
    return rows


# panel (a): H on the grid 0.02 Z, m printed to 9 decimals
rowsS = curve_data("fig01_langevin_S.dat", Q(501, 10 ** 12))
check("(D) fig01_langevin_S.dat covers -10 <= H <= 10, the plotted domain",
      Q(rowsS[0][0]) <= -10 and Q(rowsS[-1][0]) >= 10)
# panel (b): H printed to 6 decimals, |m'| <= 1/12, m to 9 decimals: 5e-7/12 + 5e-10 < 5e-8
rowsZ = curve_data("fig01_langevin_zoom.dat", Q(5, 10 ** 8))
check("(D) the curve of panel (b) starts on the bottom edge of its frame, within 1e-6",
      abs(qball(Q(rowsZ[0][1])) - (m0 - qball(Q("0.1375")))) < qball(Q(1, 10 ** 6)))
check("(D) the curve of panel (b) ends on the top edge of its frame, within 1e-6",
      abs(qball(Q(rowsZ[-1][1])) - (m0 + qball(Q("0.1375")))) < qball(Q(1, 10 ** 6)))
pts = read("fig01_points.dat")
rounded("(D) fig01_points.dat: H_0", H0, pts[0][0])
rounded("(D) fig01_points.dat: m(H_0)", m0, pts[0][1])
rounded("(D) fig01_points.dat: H_1", H1, pts[1][0])
rounded("(D) fig01_points.dat: m(H_1)", m1, pts[1][1])

# ---------------------------------------------------------------------------------------------------
print("(E) Figure 2: exact Eulerian numbers")
cent = {int(r[0]): r[1:] for r in read("fig02_centres.dat")}
NMAX = 670
check("(E) fig02_centres.dat lists n = 3, ..., 670", sorted(cent) == list(range(3, NMAX + 1)))
rounded("(E) m(H_0), printed in the text", m0, "0.44156")
rounded("(E) m(H_1), printed in the text", m1, "0.38590")
rounded("(E) Var_a(omega_3)/4 = L'(a)/4", L1(a) / 4, "0.08129")
rounded("(E) Var_b(omega_3)/4 = L'(b)/4", L1(b) / 4, "0.07562")
saved = ctx.prec
ctx.prec = 256                                                 # ample for nine decimals
u_list = [arb(1), H0.exp(), H1.exp()]
pw = [[u ** k for k in range(NMAX + 1)] for u in u_list]
TOL9 = qball(Q(5, 10 ** 10))
HALF5 = qball(Q(5, 10 ** 6))
targets = [(qball(Q("0.50000")), qball(Q("0.08333"))), (qball(Q("0.44156")), qball(Q("0.08129"))),
           (qball(Q("0.38590")), qball(Q("0.07562")))]
two_thirds = qball(Q(2, 3))
row = [1]
ok_cent, ok_text, top_ok, n_strict, n_val = True, True, True, 0, 0
for n in range(2, NMAX + 1):
    row = [(k + 1) * (row[k] if k < n - 1 else 0) + (n - k) * (row[k - 1] if k >= 1 else 0) for k in range(n)]
    if n < 3:
        continue
    E = [arb(fmpz(e)) for e in row]                            # E(n, k-1), k = 1, ..., n
    xs = [qball(Q(k, n + 1)) for k in range(1, n + 1)]
    for j in range(3):
        w = [E[k - 1] * pw[j][k] for k in range(1, n + 1)]
        Z = sum(w[1:], w[0])
        q = [wk / Z for wk in w]
        mean = sum((xk * qk for xk, qk in zip(xs, q)), arb(0))
        dev = [xk - mean for xk in xs]           # products, not ** 2: Arb's pow takes the exp-log
        var = (n + 1) * sum((dk * dk * qk for dk, qk in zip(dev, q)), arb(0))   # route at a zero midpoint
        for val, printed in ((mean, cent[n][2 * j]), (var, cent[n][2 * j + 1])):
            n_val += 1
            d = abs(val - qball(Q(printed)))
            if d < TOL9:
                n_strict += 1
            else:
                ok_cent = False
                print(f"    n = {n}, u{j}: printed {printed}, deviation {d.str(5)}")
        if n >= 10:
            tm, tv = targets[j]
            if not (abs(mean - tm) < HALF5 and abs(var - tv) < HALF5):
                ok_text = False
                print(f"    n = {n}, u{j}: centre {mean.str(8)} or width {var.str(8)} off the printed digits")
        for k, qk in enumerate(q, start=1):
            if (n, k, j) == (3, 2, 0):
                if not abs(qk - two_thirds) < arb(2) ** (-200):
                    top_ok = False
            elif not qk < two_thirds:
                top_ok = False
                print(f"    p_({n},{k})(u{j}) not below 2/3")
ctx.prec = saved
check(f"(E) all {n_val} printed centres and (n+1) x variances of fig02_centres.dat correctly rounded to nine "
      "decimals", ok_cent and n_strict == n_val == 4008)
check("(E) for every n = 10, ..., 670 the centres round to 0.50000, 0.44156, 0.38590 and the widths to "
      "0.08333, 0.08129, 0.07562, as printed in the paragraph of Figure 2", ok_text)
check("(E) p_(n,k)(u) < 2/3 for n <= 670, u = 1, e^H0, e^2H0, except the top vertex p_(3,2)(1) = 2/3", top_ok)
src2 = open(os.path.join(ROOT, "Remark_4.3_Eulerian_Histograms_Under_Field.tex")).read()
check("(E) Figure 2 draws the dashed lines at m(H_0), m(H_1) (twelve decimals) and the dotted line at 1/2",
      "(0.441559707648,0) (0.441559707648,0.7)" in src2 and "(0.385899079161,0) (0.385899079161,0.7)" in src2
      and "(0.5,0) (0.5,0.7)" in src2)

# ---------------------------------------------------------------------------------------------------
print("(F) Figure 3: Parry roots and greedy remainders")


def parry_root(n):
    """Root in (1, 2) of P(x) = x^n - x^(n-1) - 1 in an interval [lo, hi] with exact P(lo) < 0 < P(hi)."""
    x = 1.1
    for _ in range(100):
        x = x - (x ** n - x ** (n - 1) - 1) / (n * x ** (n - 1) - (n - 1) * x ** (n - 2))
    xa = arb(x)
    for _ in range(14):
        xa = (xa - (xa ** n - xa ** (n - 1) - 1) / (n * xa ** (n - 1) - (n - 1) * xa ** (n - 2))).mid()
    mid = Q(xa.mid().str(650, radius=False))
    eps = Q(1, 10 ** 580)
    lo, hi = mid - eps, mid + eps
    P = lambda t: t ** n - t ** (n - 1) - 1
    return lo, hi, (P(lo) < 0 < P(hi))


lo31, hi31, s31 = parry_root(31)
lo32, hi32, s32 = parry_root(32)
check("(F) beta_31 isolated in an interval of width 2e-580 by an exact sign change of x^31 - x^30 - 1", s31)
check("(F) beta_32 isolated in an interval of width 2e-580 by an exact sign change of x^32 - x^31 - 1", s32)
b31 = arb(qball((lo31 + hi31) / 2), qball((hi31 - lo31) / 2))
b32 = arb(qball((lo32 + hi32) / 2), qball((hi32 - lo32) / 2))
check("(F) 1 < beta_32 < beta_31 < 2", b32 > 1 and b31 > b32 and b31 < 2)
print(f"    beta_31 = {b31.str(20, radius=False)}, beta_32 = {b32.str(20, radius=False)}")


def greedy(beta, k):
    """T_beta^k(1), T(t) = beta t - floor(beta t); None if a floor is not decided by the ball."""
    t = arb(1)
    for _ in range(k):
        y = beta * t
        if y < 1:
            t = y
        elif y > 1 and y < 2:
            t = y - 1
        else:
            return None
    return t


for k in (1, 5, 10, 15, 20, 25, 30, 31):
    rows = read(f"fig06_orbit_k{k:02d}.dat")
    good, worst = True, 0.0
    for xs_, ys_, zs_ in rows:
        beta = b32 + qball(Q(xs_)) * (b31 - b32)
        t = greedy(beta, k)
        if t is None or int(ys_) != k:
            good = False
            print(f"    k = {k}, h = {xs_}: floor not decided")
            continue
        d = abs(t - qball(Q(zs_)))
        worst = max(worst, fl(d))
        if not d < qball(Q(1, 10 ** 12)):
            good = False
            print(f"    k = {k}, h = {xs_}: plotted {zs_}, Arb {t.str(12)}")
    check(f"(F) fig06_orbit_k{k:02d}.dat: {len(rows)} remainders T^{k}(1) within 1e-12, every floor decided", good)
    print(f"    k = {k}: largest deviation {worst:.3e}")
betaE = SQRT2 * (1 / SQRT2).sinh()
hE = (betaE - b32) / (b31 - b32)
sp = read("fig06_special.dat")
print(f"    beta_E = {betaE.str(20, radius=False)}, h_E = {hE.str(20, radius=False)}")
check("(F) beta_32 < beta_E < beta_31", betaE > b32 and betaE < b31)
rounded("(F) fig06_special.dat and the dashed line of Figure 3: h_E", hE, sp[0][0])
rounded("(F) caption: h_E", hE, "0.9961")
tE = greedy(betaE, 31)
check("(F) fig06_special.dat: T^31_{beta_E}(1) within 1e-12 of the plotted value, every floor decided",
      tE is not None and abs(tE - qball(Q(sp[0][2]))) < qball(Q(1, 10 ** 12)))
check("(F) T^k_{beta_31}(1) = beta_31^(k-1)(beta_31 - 1) < 1 for k = 1, ..., 30",
      all(b31 ** (j - 1) * (b31 - 1) < 1 for j in range(1, 31)))
check("(F) the thirtieth remainder at beta_31 is 1/beta_31: |beta_31^29 (beta_31 - 1) - 1/beta_31| < 1e-570",
      abs(b31 ** 29 * (b31 - 1) - 1 / b31) < qball(Q(1, 10 ** 570)))
check("(F) beta_31^30 (beta_31 - 1) = 1 within 1e-570, so T^31_{beta_31}(1) = 0 (floor convention)",
      abs(b31 ** 30 * (b31 - 1) - 1) < qball(Q(1, 10 ** 570)))
check("(F) left limit 1: on (beta_32, beta_31) T^31(1) = beta^30 (beta - 1) < 1, increasing, -> 1; "
      "exact value < 1 at the rational lo < beta_31", lo31 ** 30 * (lo31 - 1) < 1)
ep = read("fig06_endpoint.dat")
ll = read("fig06_leftlimit.dat")
check("(F) fig06_endpoint.dat = (1, 31, 0), fig06_leftlimit.dat = (1, 31, 1)",
      ep[0] == ["1", "31", "0"] and ll[0] == ["1", "31", "1"])
src3 = open(os.path.join(ROOT, "Theorem_8.1_Eulerian_Parry_Boundary.tex")).read()
check("(F) Figure 3 draws the dashed line of beta_E at h_E from z = 0 to the plotted T^31_{beta_E}(1)",
      "coordinates {(0.996073416735,31,0) (0.996073416735,31,0.999686759384684)}" in src3)

# ---------------------------------------------------------------------------------------------------
print("(G) the display of Tr(2/(2A+I)), printed to 52 decimals")
# Tr(2/(2A+I)) = coth(b)/sqrt2 - 1 (Theorem 7.2; its series form is certified in manuscript14_section7_arb.py,
# which checks the first 50 decimals); version 14.118 prints 52.
rounded("(G) Tr(2/(2A+I)) = coth(b)/sqrt2 - 1, the display (companion-t-num)", b.coth() / SQRT2 - 1,
        "0.1613630697302135425959636855281220737173049616172233")

print(f"python-flint {flint.__version__}, precision {PREC} bits, {count} checks")
if failures:
    print(f"FAILED: {len(failures)} check(s)")
    for f_ in failures:
        print("   ", f_)
    sys.exit(1)
print("ALL VERSION-14.118 SECTION 4.5 AND FIGURE 1-3 CHECKS PASSED AT 2000 BITS")
