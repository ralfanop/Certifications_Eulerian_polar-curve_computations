"""Radial minimax (V478 Thm 3.12) and planar Hausdorff minimax (V478 Thm 3.13): high-precision recomputation.

Non-rigorous: Newton solves at 110 digits plus a global scan confirming which critical
configuration is the maximiser.  Rigorous enclosure of h_* is NOT attempted here.
"""
import mpmath as mp

mp.mp.dps = 110
pi = mp.pi
q = 2 / pi
c = (1 + q) / 2
m = (1 - q) / 2

def rE(t):
    return 2 * mp.sin(t / 2) / t
def drE(t):
    return mp.cos(t / 2) / t - 2 * mp.sin(t / 2) / t**2
def gE(t):
    return mp.matrix([rE(t) * mp.cos(t), rE(t) * mp.sin(t)])
def dgE(t):
    r, dr = rE(t), drE(t)
    return mp.matrix([dr * mp.cos(t) - r * mp.sin(t), dr * mp.sin(t) + r * mp.cos(t)])
def gL(t, h):
    r = c + h + m * mp.cos(t)
    return mp.matrix([r * mp.cos(t), r * mp.sin(t)])
def dgL(t, h):
    r, dr = c + h + m * mp.cos(t), -m * mp.sin(t)
    return mp.matrix([dr * mp.cos(t) - r * mp.sin(t), dr * mp.sin(t) + r * mp.cos(t)])
def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]

# ---- Theorem 3.12 ----
F = lambda th: (2 * mp.sin(th / 2) - th * mp.cos(th / 2)) / (th**2 * mp.sin(th)) - m
th_star = mp.findroot(F, 2.0)
Delta = rE(th_star) - c - m * mp.cos(th_star)
eps_rad = Delta / 2
print("theta_*        ", mp.nstr(th_star, 60))
print("Delta          ", mp.nstr(Delta, 60))
print("eps_rad        ", mp.nstr(eps_rad, 60))
print("b_rad = c+eps  ", mp.nstr(c + eps_rad, 60))
print("a = m          ", mp.nstr(m, 60))
print("c - 2m = 3/pi-1/2 =", mp.nstr(c - 2 * m, 20))

# ---- Theorem 3.13 ----
def dist_to_body(p, h):
    """Euclidean distance from p to the filled convex limacon Omega_h (0 if inside)."""
    ang = mp.atan2(p[1], p[0])
    rad = mp.sqrt(p[0] ** 2 + p[1] ** 2)
    if rad <= c + h + m * mp.cos(ang):
        return mp.mpf(0)
    # nearest boundary point: minimise |p - gL(t)|^2 over t, start at polar angle
    g = lambda t: dot(p - gL(t, h), dgL(t, h))
    t0 = mp.findroot(g, ang)
    return mp.norm(p - gL(t0, h))

def Q(h, n=400, dps=30):
    with mp.workdps(dps):
        best, arg = mp.mpf(0), None
        for i in range(1, n):
            th = pi * i / n
            d = dist_to_body(gE(th), h)
            if d > best:
                best, arg = d, th
        return best, arg

with mp.workdps(30):
    print("Q(0) scan     :", [mp.nstr(x, 12) for x in Q(mp.mpf(0))])
    print("Q(Delta) scan :", [mp.nstr(x, 12) for x in Q(Delta)])

# Newton on the 3x3 critical system (theta, t, h)
def sysF(th, t, h):
    d = gE(th) - gL(t, h)
    return [dot(d, dgL(t, h)), dot(d, dgE(th)), dot(d, d) - h**2]
sol = mp.findroot(sysF, (mp.mpf("2.1"), mp.mpf("2.1"), mp.mpf("0.0493")))
th_h, t_h, h_star = sol
print("Hausdorff critical pair: theta_E =", mp.nstr(th_h, 40), " t_L =", mp.nstr(t_h, 40))
print("h_*  =", mp.nstr(h_star, 100))
paper = mp.mpf("0.04929794832571833570703662300396701228024147449936041418804532388531218517828559")
print("h_* - paper value =", mp.nstr(h_star - paper, 5))
print("h_* < eps_rad:", h_star < eps_rad, " ratio h_*/eps_rad =", mp.nstr(h_star / eps_rad, 20))
# global check: at h_*, scan Q(h_*) and compare with h_*
with mp.workdps(40):
    Qh, argh = Q(h_star, n=2000, dps=40)
    print("scan Q(h_*) =", mp.nstr(Qh, 25), " at theta ~", mp.nstr(argh, 8), "; h_* =", mp.nstr(h_star, 25))
# second-order check: Q(h_*) evaluated exactly at the Newton angle equals h_*
with mp.workdps(100):
    print("dist(gE(theta_h), Omega_h*) - h_* =", mp.nstr(dist_to_body(gE(th_h), h_star) - h_star, 5))
