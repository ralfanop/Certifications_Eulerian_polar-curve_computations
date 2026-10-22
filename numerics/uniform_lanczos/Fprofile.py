"""Limit profile F(alpha) = a_alpha^2/4, H(a_alpha) = alpha,
H(a) = (1/pi) int_0^{pi/2} a sin(th) I'(a sin th) dth,  I'(x) = s(x), Lambda'(s(x)) = x."""
import mpmath as mp
mp.mp.dps = 30
def Lp(s):   # Lambda'(s) = coth(s/2)/2 - 1/s
    if abs(s) < mp.mpf('1e-6'):
        return s/12 - s**3/720
    return mp.coth(s/2)/2 - 1/s
def sx(x):
    if x == 0: return mp.mpf(0)
    g = 12*x/(1-4*x*x)      # good initial guess (exact as x->0 and x->1/2 asymptotically ~ 1/(1/2-x))
    return mp.findroot(lambda s: Lp(s) - x, g)
def H(a):
    return mp.quad(lambda th: a*mp.sin(th)*sx(a*mp.sin(th)), [0, mp.pi/2]) / mp.pi
def a_of(alpha):
    return mp.findroot(lambda a: H(a) - alpha, (mp.mpf('1e-6'), mp.mpf('0.5')-mp.mpf('1e-12')), solver='anderson')
def F(alpha):
    a = a_of(alpha); return a*a/4
if __name__ == "__main__":
    for t in ['0.01','0.25','0.5','1','2','4','8','16']:
        t = mp.mpf(t); f = F(t)
        print(mp.nstr(t,4), mp.nstr(f,20), ' small-alpha 2-term:', mp.nstr(t/12-t*t/20,12))
