"""V478 §3.11: certificates for the Montgomery-Taylor decimals printed in the manuscript.

With z0 = i/sqrt2 (Eq. (4)) one has z0 coth z0 = (1/sqrt2) cot(1/sqrt2) (proved in Lean:
EulerianCert.MontgomeryTaylor.z0_coth_z0). V478 prints
    C_MT = 1/2 + z0 coth z0 = 1.3274992963...     and     3/2 - z0 coth z0 = 0.6725007...
(Lamzouri, arXiv:2609.02882v2, Eqs. (3.1) and (1.1)). A value printed as d... is certified when a
rigorous enclosure [L, U] lies in [d, d + 10^-k). Both interval backends are used.
"""
from fractions import Fraction as Fr
import mpmath as mp
import ia_fixed as fx

mp.mp.dps = 120   # so that converting interval endpoints to mpf is exact
iv = mp.iv
iv.dps = 60
x = 1 / iv.sqrt(2)
c = iv.cos(x) / iv.sin(x) / iv.sqrt(2)
cmt, c0 = iv.mpf(1) / 2 + c, iv.mpf(3) / 2 - c
print("mpmath.iv  C_MT =", cmt)
print("mpmath.iv  C_0  =", c0)

X = fx.ONE / fx.sqrt(fx.FI.frac(2))
C = fx.cos(X) / fx.sin(X) / fx.sqrt(fx.FI.frac(2))
CMT, C0 = fx.FI.frac(Fr(1, 2)) + C, fx.FI.frac(Fr(3, 2)) - C
def bounds_fx(v): return Fr(v.lo, 1 << fx.P), Fr(v.hi, 1 << fx.P)
def _exact(m):  # exact binary value of an mpf endpoint, as a Fraction
    man, ex = mp.mpf(m).man_exp
    return Fr(man) * Fr(2) ** ex
def bounds_iv(v): return _exact(v.a), _exact(v.b)

ok = True
for name, d, k, ivv, fxv in [("C_MT", Fr("1.3274992963"), 10, cmt, CMT), ("C_0", Fr("0.6725007"), 7, c0, C0)]:
    for back, (L, U) in [("mpmath.iv", bounds_iv(ivv)), ("ia_fixed", bounds_fx(fxv))]:
        good = d <= L and U < d + Fr(1, 10 ** k)
        ok &= good
        print(f"{name} = {float(d):.{k}f}... ({back}): {'certified' if good else 'FAIL'}; width {float(U - L):.1e}")
print("ALL CERTIFIED" if ok else "SOME CHECK FAILED")
