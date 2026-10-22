"""Numerical check of Milovanovic's Conjecture 2 (fixed k, m -> infinity), long double Stieltjes."""
from fractions import Fraction as Fr
import numpy as np
from beta_bspline import betas
def conj2(k, m):
    k = Fr(k); m = Fr(m)
    return (k*m/12 - k*(k-1)/20 + 4*k*(k-1)*(k-2)/(525*m) + 2*k*(k-1)*(k-2)*(5*k-9)/(2625*m*m)
            + 2*k*(k-1)*(k-2)*(552*k*k-1279*k+255)/(1010625*m**3))
for m in [50, 100, 200, 400]:
    res = betas(m, 10)
    row = []
    for k in [3, 6, 10]:
        b = res[k-1][1]
        err = float(b - np.longdouble(float(conj2(k, m))))
        row.append(f"k={k}: err={err:+.3e}, err*m^4={err*m**4:+.4f}")
    print(f"m={m}: " + "; ".join(row))
