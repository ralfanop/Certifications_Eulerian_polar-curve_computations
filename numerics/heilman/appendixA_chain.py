"""Certification of the arithmetic chain of Appendix A (S. M. Heilman, 'An explicit constant chase in the
BMMN proof') of R. Alfano, 'A second look at Braverman et al.'s Theorem' (ResearchGate, 15 June 2026).

Inputs taken as given (certified externally in Appendix A by mesh-plus-derivative / interval arithmetic,
not re-certified here):  B6 (A.14), the sup/inf values (A.28)-(A.29), (A.35)-(A.36), (A.40)-(A.41),
(A.44), (A.52), (A.56), (A.58).  Everything derived from them is re-computed here exactly.

Part II examines the role of 231 = 2n+1 (n = 115): which integers n are admissible, and whether
231 can be replaced by 232 or 233 without invalidating the conclusion K_G < K_G^R."""
import sys
from fractions import Fraction as Fr
from math import factorial
from ri import RI, c, dec, PI, SQRT2, LOG1S2, sqrt_int

results = []
def check(label, ok, detail=""):
    results.append((label, ok)); print(("PASS " if ok else "FAIL ") + label + ("  " + detail if detail else ""))

def sci(x, d=15):  # exact rational -> scientific string (display only)
    x = Fr(x); s = "-" if x < 0 else ""; x = abs(x)
    if x == 0: return "0"
    e = 0
    while x >= 10: x /= 10; e += 1
    while x < 1: x *= 10; e -= 1
    m = int(x * 10**d); return f"{s}{m // 10**d}.{str(m % 10**d).zfill(d)}e{e}"

def lower_bound_ok(I, printed):  # printed '>=' value must not exceed the true lower end
    return I.ge(dec(printed))
def upper_bound_ok(I, printed):
    return I.le(dec(printed))

print("=== Part I: the chain (A.14)-(A.80) ===")
B6 = dec("1.2843271408e17")
A = 400 * SQRT2 / PI
B = B6 / (2880 * PI)
print("A =", sci(A.lo), " B =", sci(B.lo))
check("(A.18) A = 1.80063263231421e2 (printed to 15 digits)", abs(A.lo - dec("1.80063263231421e2")) < dec("1e-12"))
check("(A.19) B = 1.41949314587084e13 (printed to 15 digits)", abs(B.lo - dec("1.41949314587084e13")) < dec("1e-1"))
eta_star_sq = 2 * A / (3 * B)
eta = dec("2.90803934947e-6")                    # the value actually fixed in (A.3), (A.21), (A.74)
check("(A.21) eta = 2.90803934947e-6 lies within 1e-17 of eta_* = sqrt(2A/3B)",
      (eta - dec("1e-17"))**2 <= eta_star_sq.lo and eta_star_sq.hi <= (eta + dec("1e-17"))**2)
check("(A.21) eta < 1e-2", eta < dec("1e-2"))
Delta = A * eta**4 - B * eta**6
print("Delta(eta) in", sci(Delta.lo), sci(Delta.hi))
check("(A.23) Delta >= 4.29244734953e-21", lower_bound_ok(Delta, "4.29244734953e-21"))

r = dec("0.92")
check("(A.28) 0.7988429115 < 4/5", dec("0.7988429115") < Fr(4, 5))
check("(A.29) 0.8282425938 < 5/6", dec("0.8282425938") < Fr(5, 6))
M092, m092 = dec("193.6822943625"), dec("0.9666807077") - r
check("(A.38) m_0.92 = 0.9666807077 - 0.92 = 0.0466807077", m092 == dec("0.0466807077"))
p092 = m092 / (2 * M092)
check("(A.39) p_0.92 = m/(2M) >= 1.20508454e-4", p092 >= dec("1.20508454e-4"), sci(p092, 12))
M096, m096 = dec("300.7944582777"), dec("0.9971640256") - dec("0.96")
p096 = m096 / (2 * M096)
check("(A.42) p_0.96 = m/(2M) >= 6.17764466e-5", p096 >= dec("6.17764466e-5"), sci(p096, 12))
Mprod = 12 * dec("381.8015394237")
check("(A.45) 12 x 381.8015394237 = 4581.6184730844 (exact)", Mprod == dec("4581.6184730844"))
check("(A.45)-(A.46) printed upper bound M = 4581.618473084 is >= 12 x 381.8015394237",
      dec("4581.618473084") >= Mprod, "exact product 4581.6184730844 exceeds the printed bound by 4e-10")
M = Mprod                                         # use the exact (larger) value from here on
R2 = Fr(6, 7)**2 + 49
check("(A.47) R <= sqrt((6/7)^2+7^2) <= 7.05228288411", dec("7.05228288411")**2 >= R2)
R = dec("7.05228288411")
Cr = 8 * M**2 * R / (1 - r)**2 * (1 + 16 * R / (1 - r)**3)
check("(A.48) C_r <= 4.07811339e16", Cr <= dec("4.07811339e16"), sci(Cr, 10))
Cr = dec("4.07811339e16")
Crp = 2 * Cr / r * (dec("0.9") / r) * (1 - dec("0.9") / r)**-2
check("(A.49) C_r' <= 2.01664948e18", Crp <= dec("2.01664948e18"), sci(Crp, 10))
Crp = dec("2.01664948e18")
L0 = 2 / sqrt_int(5)
check("(A.50) L_0 = 2/sqrt5 <= 0.894427191", upper_bound_ok(L0, "0.894427191"))
Leta = 4 * dec("8.54068663589")
check("(A.51)-(A.53) L_eta <= 4 x 8.54068663589 <= 34.1627465436", Leta <= dec("34.1627465436"), sci(Leta, 12))
L = dec("34.1627465436")
check("(A.54) L = max(L_0, L_eta) <= 34.1627465436", L0.hi <= L)
rho = dec("1.152")
check("(A.56) 0.9950381805 < 1", dec("0.9950381805") < 1)
Mphi = dec("155.0302861362")
Dl = dec("4.29244734953e-21")                     # certified lower bound for Delta
eps = dec("0.664") * Dl / L
check("(A.60) eps = 0.664 Delta/L = 8.34296222775e-23 (to 12 digits)", abs(eps - dec("8.34296222775e-23")) < dec("1e-33"), sci(eps, 14))
eps = dec("8.34296222775e-23")
q = dec("0.9") / rho
check("q = 0.9/rho = 25/32 exactly", q == Fr(25, 32))
def tail(n):  # M_phi * sum_{k>=n+1} q^(2k+1) = M_phi q^(2n+3)/(1-q^2)
    return Mphi * q**(2*n + 3) / (1 - q**2)
nmin = next(n for n in range(1000) if tail(n) < eps / 2)
check("(A.62) minimal n with tail < eps/2 is 115", nmin == 115, f"tail(114)={sci(tail(114),4)}, tail(115)={sci(tail(115),4)}, eps/2={sci(eps/2,4)}")
def p_of(m): return rho**m / (2 * factorial(m) * Mphi)
p = p_of(231)
check("(A.64) p = rho^231/(2 231! M_phi) = 2.82280900060e-436 (to 12 digits)", abs(p / dec("2.82280900060e-436") - 1) < dec("1e-11"), sci(p, 14))
def sign_control(pv, n):  # p M_phi rho^-(2k+1) < 1/(2 (2k+1)!) for k = 0..n
    return all(pv * Mphi / rho**(2*k + 1) < Fr(1, 2 * factorial(2*k + 1)) for k in range(n + 1))
check("(A.63) sign control holds for k = 0..115 with p = p(231)", sign_control(p, 115))
check("(A.64) p is below p_0.92 and p_0.96", p < p092 and p < p096)
def delta0(pv): return pv * Delta - L * (Crp * pv**2 + pv * eps)
d0 = delta0(p)
check("(A.66) delta_0 >= 4.07123102832e-457", d0.ge(dec("4.07123102832e-457")), sci(d0.lo, 14))
check("(A.66) delta_0 < 1e-100 < 0.9 - log(1+sqrt2)", d0.hi < dec("1e-100") and (0.9 - LOG1S2).gt(dec("1e-100")))
gap = PI * d0 / (2 * LOG1S2 * (LOG1S2 + d0))
check("(A.79) K_Kr - K_G >= 8.23e-457", gap.ge(dec("8.23e-457")), sci(gap.lo, 6))
KKr = PI / (2 * LOG1S2)
digits = "1.78221397819136911177441345297254934079173190977324"
check("(A.80) K_Kr = 1.78221397819136911177441345297254934079173190977324 (correctly rounded to 50 decimals; true digits ...0977323938...)",
      KKr.ge(dec(digits) - dec("5e-51")) and KKr.lt(dec(digits) + dec("5e-51")))

print("\n=== Part I-bis: the chain re-run with every bound rounded outward ===")
# (A.39), (A.45)-(A.47), (A.66) print bounds rounded in the wrong direction by about 1e-12 relative,
# and the value printed in (A.49) corresponds to [1-(0.9/r)^2]^(-1), not to the printed [1-(0.9/r)]^(-2).
Mc = Mprod                                        # 4581.6184730844
Rc = Fr(7052282884113, 10**12)                    # >= sqrt((6/7)^2+49) = 7.0522828841128...
check("outward R = 7.052282884113 >= sqrt((6/7)^2+7^2)", Rc**2 >= R2)
Crc = 8 * Mc**2 * Rc / (1 - r)**2 * (1 + 16 * Rc / (1 - r)**3)
xr = dec("0.9") / r
Crp_printed_formula = 2 * Crc / r * xr * (1 - xr)**-2
Crp_value_formula = 2 * Crc / r * xr / (1 - xr**2)
print("C_r (outward) =", sci(Crc, 10), "; C_r' with printed formula =", sci(Crp_printed_formula, 10),
      "; with [1-(0.9/r)^2]^-1 =", sci(Crp_value_formula, 10))
Crp_safe = max(Crp_printed_formula, Crp_value_formula)
d0c = p * Delta - L * (Crp_safe * p**2 + p * eps)
gapc = PI * d0c / (2 * LOG1S2 * (LOG1S2 + d0c))
check("corrected delta_0 >= 4.0712310283e-457 (the 11 digits that survive)", d0c.ge(dec("4.0712310283e-457")), sci(d0c.lo, 14))
check("corrected K_Kr - K_G >= 8.23e-457 (A.79) still holds", gapc.ge(dec("8.23e-457")), sci(gapc.lo, 8))
check("sign control at k = 115 for p = p(231) holds with equality at the level of the bounds",
      p * Mphi / rho**231 == Fr(1, 2 * factorial(231)),
      "strictness requires sup|phi| < M_phi strictly on |z| = rho")

print("\n=== Part II: the role of 231 = 2n+1 ===")
pmax_delta = (Dl - L * eps) / (L * Crp)          # delta_0 > 0  iff  p < (Delta - L eps)/(L C_r')
print("delta_0 > 0 for every p in (0, (Delta-L eps)/(L C_r')) =", sci(pmax_delta, 6))
for m in (232, 233, 234, 235, 241, 301):
    pv = p_of(m)
    n_needed = 115                                # sign control is required for k = 0..n, n >= 115
    sc = sign_control(pv, n_needed)
    d = delta0(pv); g = PI * d / (2 * LOG1S2 * (LOG1S2 + d))
    ok = sc and d.gt(0) and pv < p092 and pv < p096
    check(f"m = {m}: p = rho^m/(2 m! M_phi) = {sci(pv,4)}; sign control k<=115 and delta_0 > 0", ok,
          f"delta_0 >= {sci(d.lo,4)}, K_Kr - K_G >= {sci(g.lo,4)}")
check("m = 230 (p larger than p(231)) violates sign control at k = 115", not sign_control(p_of(230), 115))
check("n = 114 is impossible for every admissible eps (eps < Delta/L, needed for delta_0 > 0), given the certified Delta, L, M_phi, rho",
      tail(114) >= Delta.hi / (2 * L), f"tail(114) = {sci(tail(114),4)} >= Delta/(2L) = {sci(Delta.hi/(2*L),4)}")
print("\nminimal n as a function of the free factor c in eps = c Delta/L (rho, M_phi fixed):")
for cf in ("0.1", "0.3", "0.5", "0.664", "0.8", "0.9", "0.99"):
    e = dec(cf) * Dl / L
    n_c = next(n for n in range(1000) if tail(n) < e / 2)
    print(f"  c = {cf:>5}:  n_min = {n_c},  2n+1 = {2*n_c+1}")

print(f"\n{sum(ok for _, ok in results)}/{len(results)} checks passed")
sys.exit(0 if all(ok for _, ok in results) else 1)
