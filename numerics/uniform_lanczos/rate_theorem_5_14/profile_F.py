"""Profile F(t) = xi_t^2/4, Phi(xi_t) = t, Phi(a) = (1/pi) int_0^{pi/2} a sin(th) I'(a sin th) dth,
I' = inverse of Lambda'(s) = coth(s/2)/2 - 1/s.  Double precision; Gauss-Legendre in theta."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq

def Lp(s):
    s = np.asarray(s, float); out = np.empty_like(s); sm = np.abs(s) < 1e-3
    z = s[sm]; out[sm] = z/12 - z**3/720 + z**5/30240
    z = s[~sm]; out[~sm] = 0.5/np.tanh(z/2) - 1/z
    return out

def Lpp(s):
    s = np.asarray(s, float); out = np.empty_like(s); sm = np.abs(s) < 1e-3
    z = s[sm]; out[sm] = 1/12 - z**2/240 + z**4/6048
    z = s[~sm]; out[~sm] = 1/z**2 - 1/(4*np.sinh(z/2)**2)
    return out

def Ip(x):
    # bisection on the bracket 12|x| <= s <= 1/(1/2-|x|)  (Lemma 5.3 bounds); odd extension
    x = np.asarray(x, float); ax = np.abs(x)
    lo = np.maximum(12*ax*0, np.maximum(1/(0.5 - ax) - 2, 0)); hi = 1/(0.5 - ax) + 12*ax
    for _ in range(70):
        mid = (lo + hi)/2; f = Lp(mid) - ax
        lo = np.where(f < 0, mid, lo); hi = np.where(f < 0, hi, mid)
    return np.sign(x)*(lo + hi)/2

xg, wg = leggauss(400)
th = (xg + 1)*np.pi/4; wth = wg*np.pi/4
def Phi(a):
    y = a*np.sin(th)
    return np.sum(wth*y*Ip(y))/np.pi

def xi(t): return brentq(lambda a: Phi(a) - t, 1e-12, 0.5 - 1e-12, xtol=1e-15)
def F(t): return xi(t)**2/4

if __name__ == "__main__":
    for t in [0.25, 0.5, 1, 2, 4]:
        print(t, "%.7f" % F(t))
