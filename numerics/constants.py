"""High-precision recomputation of the closed-form constants of the V478 manuscript.

Non-rigorous cross-check (mpmath, 120 digits); rigorous enclosures are in si_enclosure.py.
"""
import mpmath as mp

mp.mp.dps = 120
pi = mp.pi
Si = mp.si

def rE(t):
    t = mp.mpf(t)
    return mp.mpf(1) if t == 0 else 2 * mp.sin(t / 2) / t

A0 = 4 / pi * Si(pi / 2)
def A(n):
    return 2 / pi * (Si(pi / 2 * (2 * n + 1)) - Si(pi / 2 * (2 * n - 1)))

bE = A0 / 2
aE = A(1)
err1 = bE - aE - 2 / pi
Etot = 4 / pi * Si(pi) - 8 / pi**2
# Parseval check via quadrature
Etot_quad = mp.quad(lambda t: rE(t) ** 2, [-pi, 0, pi]) / pi
rms = mp.sqrt((Etot - A0**2 / 2 - aE**2) / 2)
rel = pi / 2 * err1 * 100
tab1 = 100 * A0**2 / (2 * Etot)
tab2 = 100 * (A0**2 + 2 * aE**2) / (2 * Etot)
tab3 = 100 * aE**2 / (Etot - A0**2 / 2)
varthetaE_deg = 2 * mp.acot(pi) * 180 / pi

# Check of the A_n integral representation and bounds for a few n
rows = []
for n in [1, 2, 3, 10, 50]:
    An = A(n)
    alt = (-1) ** (n + 1) * 4 / pi * mp.quad(lambda s: s * mp.sin(s) / (n**2 * pi**2 - s**2), [0, pi / 2])
    lo = 4 / (pi**3 * n**2)
    hi = 4 / (pi**3 * (n**2 - mp.mpf(1) / 4))
    rows.append((n, mp.nstr(An, 20), mp.nstr(An - alt, 5), lo < abs(An) < hi))

# Tail sum identity E_1 = sum_{n>=2} |A_n| (partial check with Richardson-free bound)
tail = mp.nsum(lambda n: abs(A(int(n))), [2, mp.inf])

out = {
    "A0": A0, "bE": bE, "aE": aE, "err1 = bE-aE-2/pi": err1, "tail sum_{n>=2}|A_n|": tail,
    "Etot closed form": Etot, "Etot quadrature": Etot_quad, "rms": rms, "relative endpoint %": rel,
    "table: const %": tab1, "table: const+cos %": tab2, "table: variation %": tab3,
    "vartheta_E (deg)": varthetaE_deg, "half-angle arccot(pi) rad": mp.acot(pi),
    "uniform bound N=1 (2/pi)^3/3": (2 / pi) ** 3 / 3,
}
if __name__ == "__main__":
    for k, v in out.items():
        print(f"{k:32s} {mp.nstr(v, 90)}")
    print("n, A_n, (A_n - integral rep), strict bounds hold")
    for r in rows:
        print("  ", r)
