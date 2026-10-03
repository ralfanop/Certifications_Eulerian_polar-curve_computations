"""Recompute D_kappa (V478 Eqs. 49-50) by an independent route (non-rigorous, ~35 digits).

By symmetry u -> 1-u, D^2 = 2 * int_{1/2}^{1} (kE(u)-kL(u))^2 du, with u = 1/2 + s(theta)/L.
We change variables to the Eulerian angle theta in (0, pi):
   D^2 = 2 * int_0^pi (kE(theta) - kL(thetaL(theta)))^2 * speedE(theta)/L_E dtheta,
where thetaL(theta) solves s_L(thetaL)/L_L = s_E(theta)/L_E (half-arcs measured from theta=0).
"""
import mpmath as mp

mp.mp.dps = 45
pi = mp.pi
bE = 2 / pi * mp.si(pi / 2)
aE = 2 / pi * (mp.si(3 * pi / 2) - mp.si(pi / 2))

def rE(t):
    if abs(t) < mp.mpf(10) ** (-8):
        return 1 - t**2 / 24 + t**4 / 1920
    return 2 * mp.sin(t / 2) / t
def drE(t):
    if abs(t) < mp.mpf(10) ** (-8):
        return -t / 12 + t**3 / 480
    return mp.cos(t / 2) / t - 2 * mp.sin(t / 2) / t**2
def d2rE(t):
    if abs(t) < mp.mpf(10) ** (-8):
        return -mp.mpf(1) / 12 + t**2 / 160
    return -mp.sin(t / 2) / (2 * t) - 2 * mp.cos(t / 2) / t**2 + 4 * mp.sin(t / 2) / t**3

rL = lambda t: bE + aE * mp.cos(t)
drL = lambda t: -aE * mp.sin(t)
d2rL = lambda t: -aE * mp.cos(t)

def kappa(r, dr, d2r, t):
    R, D1, D2 = r(t), dr(t), d2r(t)
    return abs(R**2 + 2 * D1**2 - R * D2) / (R**2 + D1**2) ** mp.mpf(1.5)
def speed(r, dr, t):
    return mp.sqrt(r(t) ** 2 + dr(t) ** 2)

sE = lambda t: mp.quad(lambda x: speed(rE, drE, x), [0, t])
sL = lambda t: mp.quad(lambda x: speed(rL, drL, x), [0, t])
LE2, LL2 = sE(pi), sL(pi)  # half lengths

def thetaL_of(theta):
    target = sE(theta) / LE2 * LL2
    return mp.findroot(lambda x: sL(x) - target, theta, df=lambda x: speed(rL, drL, x))

def integrand(theta):
    tl = thetaL_of(theta)
    return (kappa(rE, drE, d2rE, theta) - kappa(rL, drL, d2rL, tl)) ** 2 * speed(rE, drE, theta) / LE2

mp.mp.dps = 40
D2 = mp.quad(integrand, [0, pi / 2, pi])  # = int_{1/2}^{1}... times 2 handled: (1/2)*2
# int_{1/2}^1 (.)^2 du = int_0^pi (.)^2 speedE/(2*LE2) dtheta ; times 2 for symmetry -> int_0^pi (.)^2 speedE/LE2... /? see below
# u = 1/2 + sE(theta)/(2*LE2) so du = speedE/(2*LE2) dtheta; D^2 = 2*int = int_0^pi (.)^2 speedE/LE2 dtheta.
Dk = mp.sqrt(D2)
print("L_E =", mp.nstr(2 * LE2, 30), " L_L =", mp.nstr(2 * LL2, 30))
print("D_kappa =", mp.nstr(Dk, 32))
print("paper   = 0.203783759536049443826081")
print("diff    =", mp.nstr(Dk - mp.mpf("0.203783759536049443826081"), 5))
# smooth turning check (V478 Eq. 39): int kappa ds over the open arc = 2 pi + vartheta_E
turn = 2 * mp.quad(lambda t: (rE(t)**2 + 2*drE(t)**2 - rE(t)*d2rE(t)) / (rE(t)**2 + drE(t)**2), [0, pi])
print("smooth turning - (2pi + 2 arccot pi) =", mp.nstr(turn - (2 * pi + 2 * mp.acot(pi)), 5))
