"""Rigorous enclosures for Theorems 3.12-3.13 of the V478 manuscript and certification of every
related printed decimal, on two independent backends (mpmath.iv and ia_fixed).

Theorem 3.12.  theta -> f'(cos theta) - m is strictly increasing on (0, pi) (f is strictly concave
by Eqs. (62)-(64), and cos is decreasing), so a sign change of
    S(theta) = (2 sin(theta/2) - theta cos(theta/2)) / (theta^2 sin theta) - m      (Eq. 59)
on [t0, t1] encloses theta_*.  Delta = max (f - l) = g(theta_*), g(theta) = r_E(theta) - c - m cos(theta),
is enclosed by evaluating g on [t0, t1]; eps_rad = Delta/2, b_rad = c + eps_rad.

Theorem 3.13.  h_* lies in (L, U) = (D80 - 1/2 10^-80, D80 + 1/2 10^-80) by the certificate of
hstar_cert.py (stored in hstar_certificate.json); b_H = c + h_*.

Printed decimals "approx d" must have their enclosure inside the rounding cell of d; values printed
as "d..." inside [d, d + 10^-k).  All comparisons are exact (Fractions).
"""
import contextlib, io, json, time
from fractions import Fraction as Fr
import mpmath as mp
from mpmath import iv, libmp
import ia_fixed as F

t_start = time.time()
cert = json.load(open("hstar_certificate.json"))
HL, HU = Fr(cert["L"]), Fr(cert["U"])          # L < h_* < U

with contextlib.redirect_stdout(io.StringIO()):
    import si_enclosure as SE                   # b_E - a_E - 2/pi (mpmath.iv)
    import si_enclosure_fx as SEF               # the same with ia_fixed

# non-rigorous locator for theta_* (only used to choose the bracket [t0, t1])
mp.mp.dps = 90
qq = 2 / mp.pi; mm = (1 - qq) / 2
ths = mp.findroot(lambda t: (2*mp.sin(t/2) - t*mp.cos(t/2))/(t**2*mp.sin(t)) - mm, 2.1)
t0 = Fr(mp.nstr(ths - mp.mpf(10)**-70, 85))
t1 = Fr(mp.nstr(ths + mp.mpf(10)**-70, 85))

# ---------------------------------------------------------------- backend 1: mpmath.iv
def run_mp():
    iv.dps = 90
    PI = iv.pi; q = 2 / PI; c = (1 + q) / 2; m = (1 - q) / 2
    S = lambda th: (2 * iv.sin(th / 2) - th * iv.cos(th / 2)) / (th**2 * iv.sin(th)) - m
    T0 = iv.mpf(t0.numerator) / t0.denominator     # outward-rounded enclosures of t0, t1
    T1 = iv.mpf(t1.numerator) / t1.denominator
    sign_ok = S(T0).b < 0 < S(T1).a
    T = iv.mpf([T0.a, T1.b])
    Delta = 2 * iv.sin(T / 2) / T - c - m * iv.cos(T)
    fr = lambda x: (Fr(*libmp.to_rational(x._mpi_[0])), Fr(*libmp.to_rational(x._mpi_[1])))
    return dict(sign_ok=sign_ok, theta=fr(T), Delta=fr(Delta), c=fr(c), m=fr(m), err1=fr(SE.err1))

# ---------------------------------------------------------------- backend 2: ia_fixed
def run_fx():
    PI = F.PI; q = 2 / PI; c = (1 + q) / 2; m = (1 - q) / 2
    S = lambda th: (2 * F.sin(th / 2) - th * F.cos(th / 2)) / (th**2 * F.sin(th)) - m
    T0, T1 = F.FI.frac(t0), F.FI.frac(t1)
    sign_ok = S(T0).hi < 0 < S(T1).lo
    T = F.FI.hull(T0, T1)
    Delta = 2 * F.sin(T / 2) / T - c - m * F.cos(T)
    return dict(sign_ok=sign_ok, theta=T.to_fraction_bounds(), Delta=Delta.to_fraction_bounds(),
                c=c.to_fraction_bounds(), m=m.to_fraction_bounds(),
                err1=SEF.err1.to_fraction_bounds())

def cell(lo, hi, dec):
    d = Fr(dec); nd = len(dec.split(".")[1]); h = Fr(1, 2 * 10**nd)
    return d - h < lo and hi < d + h

def trunc(lo, hi, dec):
    d = Fr(dec); nd = len(dec.split(".")[1])
    return d <= lo and hi < d + Fr(1, 10**nd)

def report(name, R):
    print(f"--- backend: {name}")
    (thl, thh), (Dl, Dh), (cl, ch), (el, eh) = R["theta"], R["Delta"], R["c"], R["err1"]
    epl, eph = Dl / 2, Dh / 2
    rows = [
        ("theta_*  (Eq. 59)", cell(thl, thh, "2.10258309466509376393"), "2.10258309466509376393"),
        ("Delta    (Eq. 60)", cell(Dl, Dh, "0.09953351643838914835807"), "0.09953351643838914835807"),
        ("eps_rad  (Eq. 60)", cell(epl, eph, "0.04976675821919457417904"), "0.04976675821919457417904"),
        ("b_rad    (Eq. 61)", cell(cl + epl, ch + eph, "0.86807664440298524572"), "0.86807664440298524572"),
        ("h_*      (Eq. 70)", cell(HL, HU, "0.04929794832571833571"), "0.04929794832571833571"),
        ("b_H      (Eq. 70)", cell(cl + HL, ch + HU, "0.86760783450950900724"), "0.86760783450950900724"),
        ("h_*      (abstract, Sec. 1) 0.0492979...", trunc(HL, HU, "0.0492979"), ""),
        ("eps_rad  (abstract, Sec. 1) 0.0497667...", trunc(epl, eph, "0.0497667"), ""),
    ]
    rows.append(("negative control: eps_rad truncated (earlier draft)",
                 cell(epl, eph, "0.04976675821919457417903"), "0.04976675821919457417903"))
    print(f"sign change of S on [t0, t1] (encloses theta_*): {R['sign_ok']}")
    for label, ok, dec in rows:
        print(f"{label:44s} {dec:28s} certified={ok}")
    # Eq. (71) and the comparisons stated after Theorem 3.13
    print(f"h_* < eps_rad (Eq. 71): {HU < epl}   margin > {float(epl - HU):.6e}")
    ml, mh = R["m"]
    print(f"b_H > 2 a_H > 0 (Eq. 71), a_H = m: {cl + HL > 2 * mh and ml > 0}")
    # 1 - h_*/eps_rad rounds to 0.94 %; 1 - h_*/(b_E - a_E - 2/pi) is about 42 %
    g1 = (1 - HU / epl, 1 - HL / eph)
    g2 = (1 - HU / el, 1 - HL / eh)
    print(f"gain over radial optimum 100(1 - h_*/eps_rad) in [{float(100*g1[0]):.6f}, {float(100*g1[1]):.6f}] %:"
          f" rounds to 0.94 % = {cell(100*g1[0], 100*g1[1], '0.94')}")
    print(f"gain over projection 100(1 - h_*/(b_E-a_E-2/pi)) in [{float(100*g2[0]):.4f}, {float(100*g2[1]):.4f}] %:"
          f" 'about 42 %' (in [41.5, 42.5)) = {Fr(83, 2) <= 100*g2[0] and 100*g2[1] < Fr(85, 2)}")
    print(f"theta_* enclosure width {float(thh - thl):.2e}; Delta enclosure width {float(Dh - Dl):.2e}")

report("mpmath.iv, 90 digits", run_mp())
report(f"ia_fixed, {F.P}-bit fixed point", run_fx())
print(f"elapsed {time.time() - t_start:.1f}s")
