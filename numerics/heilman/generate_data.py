"""Data tables behind Section 3 of "A second look at Braverman et al.'s Theorem".

Writes numerics/heilman/data/*.csv. Every number is computed in exact rational
(interval) arithmetic with ri.py, and decimals are printed with directed rounding:
a column named *_lo is rounded down, *_hi is rounded up, and anything else is
rounded to nearest. Only the formatting is decimal.

Run: python3 generate_data.py
"""
import csv, os, sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as F
from math import factorial
from ri import PI, LOG1S2, SQRT2, dec

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
os.makedirs(OUT, exist_ok=True)


def fsci(x, d=12, mode="near"):
    """Exact rational x > 0 -> decimal string with d significant digits, rounded in direction mode."""
    x = F(x)
    if x == 0:
        return "0"
    neg = x < 0
    x = abs(x)
    if neg and mode in ("down", "up"):
        mode = "up" if mode == "down" else "down"
    e = len(str(x.numerator)) - len(str(x.denominator))
    while F(10) ** e > x:
        e -= 1
    while F(10) ** (e + 1) <= x:
        e += 1
    y = x / F(10) ** (e - d + 1)                 # 10^(d-1) <= y < 10^d
    n, r = divmod(y.numerator, y.denominator)
    if mode == "up" and r:
        n += 1
    elif mode == "near" and 2 * r >= y.denominator:
        n += 1
    if n == 10 ** d:
        n //= 10
        e += 1
    s = str(n)
    s = s[0] + ("." + s[1:] if d > 1 else "")
    return ("-" if neg else "") + s + "e" + str(e)


def write(name, header, rows):
    with open(os.path.join(OUT, name), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        w.writerows(rows)
    print(f"{name}: {len(rows)} rows")


# Certified inputs of Appendix A (see appendixA_chain.py)
B6, eta = dec("1.2843271408e17"), dec("2.90803934947e-6")
Delta = 400 * SQRT2 / PI * eta**4 - B6 / (2880 * PI) * eta**6       # interval
L, rho, Mphi = dec("34.1627465436"), dec("1.152"), dec("155.0302861362")
EPS = dec("8.34296222775e-23")                                        # (A.60)
Cs = F(184) * 10**18                                                  # >= C_r' under either formula (A.49)
q = dec("0.9") / rho                                                  # 25/32
assert q == F(25, 32)
p092 = dec("0.0466807077") / (2 * dec("193.6822943625"))
p096 = dec("0.0371640256") / (2 * dec("300.7944582777"))


def tail(n):
    return Mphi * q ** (2 * n + 3) / (1 - q * q)


def p(m):
    return rho**m / (2 * factorial(m) * Mphi)


def ratio(m, k):
    """Sign-control ratio p(m) M_phi rho^-(2k+1) / [2 (2k+1)!]^-1; (A.63) requires < 1."""
    return p(m) * Mphi / rho ** (2 * k + 1) * 2 * factorial(2 * k + 1)


def delta0(m, eps):
    """Interval for delta_0 = p Delta - L (C' p^2 + p eps), with C' <= Cs."""
    pv = p(m)
    return pv * Delta - L * (Cs * pv**2 + pv * eps)


def gap(d):
    """Interval for pi delta_0 / (2 log(1+sqrt2) [log(1+sqrt2) + delta_0]), (A.79)."""
    return PI * d / (2 * LOG1S2 * (LOG1S2 + d))


def c_of(n):
    """Interval for c(n) = 2 L tail(n) / Delta: tail(n) < eps/2 iff c = L eps / Delta > c(n)."""
    return 2 * L * tail(n) / Delta


# 1. tail(n) and the threshold c(n)
rows = []
for n in range(100, 131):
    cn = c_of(n)
    rows.append([n, 2 * n + 1, fsci(tail(n), 15), fsci(cn.lo, 12, "down"), fsci(cn.hi, 12, "up"),
                 "yes" if tail(n) < EPS / 2 else "no", "yes" if cn.hi < 1 else ("no" if cn.lo >= 1 else "?")])
write("tail_vs_n.csv",
      ["n", "2n+1", "tail(n)=M_phi q^(2n+3)/(1-q^2)", "c(n)_lo", "c(n)_hi",
       "tail(n)<eps/2 for eps of (A.60)", "admissible for some c<1"], rows)

# 2. sign-control ratios R(m,k), k = 0..115
ms = list(range(229, 242))
rows = []
for k in range(116):
    rows.append([k, 2 * k + 1] + [fsci(ratio(m, k), 10) for m in ms])
write("sign_control_ratios.csv", ["k", "2k+1"] + [f"R(m={m},k)" for m in ms], rows)
rows = []
for m in ms:
    r = ratio(m, 115)
    rows.append([m, fsci(r, 15), "<1" if r < 1 else ("=1" if r == 1 else ">1"),
                 "holds strictly" if r < 1 else ("equality at k=115" if r == 1 else "fails")])
write("sign_control_at_k115.csv", ["m", "R(m,115)", "comparison", "sign control k=0..115"], rows)

# 3. delta_0 and the gap for m = 231..260, with eps of (A.60) and with the optimal eps -> c0 Delta/L
rows = []
for m in list(range(231, 261)) + [281, 301, 351, 401]:
    d = delta0(m, EPS)
    ds = p(m) * (Delta - 2 * L * tail(115)) - L * Cs * p(m) ** 2      # supremum over eps, n = 115
    rows.append([m, fsci(p(m), 12), "yes" if (p(m) < p092 and p(m) < p096) else "no",
                 fsci(d.lo, 12, "down"), fsci(gap(d).lo, 12, "down"),
                 fsci(ds.lo, 12, "down"), fsci(gap(ds).lo, 12, "down")])
write("delta0_vs_m.csv",
      ["m", "p(m)", "p(m)<p_0.92 and p_0.96", "delta0_lo (eps of A.60)", "gap_lo (eps of A.60)",
       "sup_eps delta0_lo", "sup_eps gap_lo"], rows)

# 4. n_min, m = 2n_min+1 and the resulting delta_0 as functions of c in eps = c Delta_lo / L
Dl = dec("4.29244734953e-21")
rows = []
cs = [F(i, 100) for i in range(1, 100)] + [dec("0.664"), dec("0.66328"), dec("0.66329")]
for c in sorted(set(cs)):
    e = c * Dl / L
    n = next(n for n in range(10**4) if tail(n) < e / 2)
    m = 2 * n + 1
    d = delta0(m, e)
    rows.append([fsci(c, 5), n, m, fsci(d.lo, 6, "down") if d.lo > 0 else "<=0",
                 fsci(gap(d).lo, 6, "down") if d.lo > 0 else "-"])
write("nmin_vs_c.csv", ["c", "n_min", "m=2n_min+1", "delta0_lo", "gap_lo"], rows)

# 5. printed values of Appendix A against exact values
cr = dec("4.07811339e16"); r = dec("0.92"); x = dec("0.9") / r
rows = [
    ["(A.39)", "p_0.92 >=", "1.20508454e-4", fsci(p092, 13), "printed lower bound exceeds the exact value"],
    ["(A.45)-(A.46)", "M = 12 x 381.8015394237 <=", "4581.618473084", fsci(12 * dec("381.8015394237"), 14),
     "exact product exceeds the printed bound"],
    ["(A.47)", "R <= sqrt((6/7)^2+7^2) <=", "7.05228288411", "7.0522828841128...", "printed bound below the root"],
    ["(A.49)", "C_r' <=", "2.01664948e18", fsci(2 * cr / r * x / (1 - x) ** 2, 11),
     "printed formula [1-(0.9/r)]^-2 is a typo; the printed value is that of [1-(0.9/r)^2]^-1 = " + fsci(2 * cr / r * x / (1 - x * x), 11) + ", as in Braverman et al. (5.21)"],
    ["(A.63)", "p(231) M_phi rho^-231 < 1/(2 231!)", "strict", "equality",
     "harmless: Braverman et al. (5.20) needs only p|c_{2k+1}| <= |b_{2k+1}|, which holds with a factor 2 of margin"],
    ["(A.66)", "delta_0 >=", "4.07123102832e-457", fsci(delta0(231, EPS).lo, 15, "down"),
     "printed lower bound exceeds the exact value; 11 digits survive"],
]
write("printed_slips.csv", ["equation", "quantity", "printed", "exact", "note"], rows)


# 6. The relaxed sign control of Braverman et al. (5.20): p |c_{2k+1}| <= |b_{2k+1}| suffices,
#    so p may be taken as phat(m) = rho^m / (m! M_phi) = 2 p(m).
rows = []
for m in list(range(231, 241)) + [301]:
    ph = 2 * p(m)
    d = ph * Delta - L * (Cs * ph**2 + ph * EPS)
    ds = ph * (Delta - 2 * L * tail(115)) - L * Cs * ph**2
    rows.append([m, fsci(ph, 12), "yes" if all(ph * Mphi / rho ** (2 * k + 1) <= F(1, factorial(2 * k + 1)) for k in range(116)) else "no",
                 fsci(d.lo, 12, "down"), fsci(gap(d).lo, 12, "down"), fsci(ds.lo, 12, "down"), fsci(gap(ds).lo, 12, "down")])
write("relaxed_phat_vs_m.csv",
      ["m", "phat(m)=2p(m)", "relaxed sign control k<=115", "delta0_lo (eps of A.60)", "gap_lo (eps of A.60)",
       "sup_eps delta0_lo", "sup_eps gap_lo"], rows)
