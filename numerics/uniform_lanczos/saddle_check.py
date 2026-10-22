"""Numerical check of Lemma 1: R(x) = log g_M(x) + M I(x) - 1/2 log(M/(2 pi v(x))) and R', R''
via the exact B-spline identities (Milovanovic's phi_m on [0,m]):
   phi_m'(y) = phi_{m-1}(y) - phi_{m-1}(y-1),
   phi_m''(y) = phi_{m-2}(y) - 2 phi_{m-2}(y-1) + phi_{m-2}(y-2),
g_M(x) = M phi_M(Mx + M/2).  B-spline values in long double; I, v via mpmath."""
import numpy as np, mpmath as mp
from beta_bspline import bspline_values
mp.mp.dps = 40
LD = np.longdouble
def phi(m, y):     # order-m cardinal B-spline at y (long double)
    k = int(np.floor(y)); tau = LD(y) - k
    if k < 0 or k >= m: return LD(0)
    return bspline_values(m, np.array([tau], dtype=LD))[0, k]
def Lp(s):  return mp.coth(s/2)/2 - 1/s
def Lpp(s): return 1/s**2 - 1/(4*mp.sinh(s/2)**2)
def sx(x):  return mp.findroot(lambda s: Lp(s) - x, 12*x/(1-4*x*x))
def Ifun(x):
    s = sx(x); return s*x - mp.log(mp.sinh(s/2)/(s/2))
def lead(M, x):    # -M I(x) + 1/2 log(M/(2 pi v))
    s = sx(x); return -M*Ifun(x) + mp.log(M/(2*mp.pi*Lpp(s)))/2
for x in ['0.05', '0.15', '0.25', '0.35', '0.42']:
    x = mp.mpf(x)
    Bv = lambda t: -mp.log(2*mp.pi*Lpp(sx(t)))/2          # 1/2 log(1/(2 pi v))
    d1 = -mp.diff(Ifun, x); d2 = -mp.diff(Ifun, x, 2)      # derivatives of -I
    e1 = mp.diff(Bv, x); e2 = mp.diff(Bv, x, 2)
    row = []
    for M in [50, 100, 200, 400, 800]:
        # y = M x + M/2 in [0,M]; choose x so that y is not a knot (generic)
        y = mp.mpf(M)*x + mp.mpf(M)/2
        yl = LD(mp.nstr(y, 30))
        f0 = phi(M, yl); f1 = phi(M-1, yl) - phi(M-1, yl-1)
        f2 = phi(M-2, yl) - 2*phi(M-2, yl-1) + phi(M-2, yl-2)
        L0 = mp.log(M) + mp.log(mp.mpf(str(f0)))
        L1 = M * mp.mpf(str(f1/f0))
        L2 = M*M * (mp.mpf(str(f2/f0)) - mp.mpf(str(f1/f0))**2)
        R0 = L0 - lead(M, x); R1 = L1 - (M*d1 + e1); R2 = L2 - (M*d2 + e2)
        row.append((M, float(M*R0), float(M*R1), float(M*R2)))
    print('x =', mp.nstr(x, 3), ' (M, M*R, M*R\', M*R\'\'):', [(m, round(a,5), round(b,5), round(c,5)) for m,a,b,c in row], flush=True)
