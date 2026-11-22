#!/usr/bin/env python3
"""
Manuscript 15 -- FLINT/Arb certification of the decimal constants of
equations (293)-(296), (300), (365)-(369) and (411)-(414).

Every constant is enclosed in an Arb ball at a working precision of
PREC bits (default 3,600,000) by two independent routes (A and B) that
share no formula and, where possible, no algorithm.  For each route the
script determines, by exact integer arithmetic on the endpoints of the
ball, whether the correctly rounded value to D decimal places
(default 1,000,001) is uniquely determined; it then requires the two
routes to give identical rounded strings.  The rounded digits are
written to digits/<key>.txt and every check is recorded in the log.

Route A (primary formulas of the manuscript)
  u_*         interval Newton (Moore) on f(u) = u sinh u - cosh u
  lambda_CL   1/sinh u_*
  alpha_CL    2 arctan(1/lambda_CL) rad, times 180/pi in degrees
  L_*/a       2/lambda_CL
  q           2/pi, pi by Arb (Chudnovsky)
  W_1, W_2^2  q - 1/2,  5/6 - 2 q^2,  W_2 = sqrt(W_2^2)
  W_inf       sqrt(1-q^2) - q arccos q
  D_5         (62/75) zeta(3) - 8/pi^2, zeta(3) by Arb
  magnetic    W_1(x) = 1 - tanh(x/2)/x,  W_2(x) = sqrt(1 - 2 L(x)/x),
              L(x) = coth x - 1/x,  x = 1/sqrt 8 and 1/sqrt 2

Route B (independent formulas)
  lambda_CL   interval Newton on Laplace's classical equation
              g(l) = l exp(sqrt(1+l^2)) - 1 - sqrt(1+l^2)
  u_*         sqrt(1 + lambda_CL^2)          (= coth u_* = u_*)
  alpha_CL    pi - 2 arctan(lambda_CL), pi by Machin's formula
  L_*/a       2 sinh(u_*)
  q           2/pi, pi = 16 arctan(1/5) - 4 arctan(1/239)
  W_2^2       1/3 - 2 W_1 - 2 W_1^2          (manuscript Eq. (351))
  W_inf       sqrt(1-q^2) - q arctan(sqrt(1-q^2)/q)
  D_5         zeta(3) by an independent binary-splitting evaluation of
              the Amdeberhan--Zeilberger series, with explicit tail bound
  magnetic    exp-based: tanh(x/2) = (cosh x - 1)/sinh x,
              2 L(x)/x = 2 (x cosh x - sinh x)/(x^2 sinh x),
              x = sqrt(2)/4 and sqrt(2)/2

Usage:  python3 m15_arb_certify.py [--prec BITS] [--digits D] [--out DIR]
"""

import argparse
import hashlib
import json
import os
import platform
import sys
import time

import flint
from flint import arb, ctx, fmpz

# --------------------------------------------------------------------------
# Exact decimal rounding of an Arb ball
# --------------------------------------------------------------------------


def _endpoints(x):
    """Exact endpoints of the ball x as (lo, hi, e): x subset [lo 2^e, hi 2^e]."""
    if not x.is_finite():
        raise ValueError("non-finite ball")
    mm, me = x.mid().man_exp()
    rm, re = x.rad().man_exp()
    mm, me, rm, re = fmpz(mm), int(me), fmpz(rm), int(re)
    if mm == 0:
        me = re
    if rm == 0:
        re = me
    e = min(me, re)
    M = mm * (fmpz(1) << (me - e))
    R = rm * (fmpz(1) << (re - e))
    return M - R, M + R, e


def _round_half_up(A, e, T):
    """floor(A 2^e T + 1/2) for an integer A, exponent e, positive integer T."""
    if e >= 0:
        return A * (fmpz(1) << e) * T
    s = -e
    return (2 * A * T + (fmpz(1) << s)) // (fmpz(1) << (s + 1))


def _floor(A, e, T):
    if e >= 0:
        return A * (fmpz(1) << e) * T
    return (A * T) // (fmpz(1) << (-e))


def _fmt(N, D):
    neg = N < 0
    s = str(abs(N))
    if len(s) <= D:
        s = "0" * (D - len(s) + 1) + s
    out = s[:-D] + "." + s[-D:]
    return ("-" if neg else "") + out


def certified_rounding(x, D):
    """Return (string, certified) for the value of x rounded to D decimals."""
    lo, hi, e = _endpoints(x)
    T = fmpz(10) ** D
    a = _round_half_up(lo, e, T)
    b = _round_half_up(hi, e, T)
    return _fmt(a, D), bool(a == b)


def certified_truncation(x, D):
    lo, hi, e = _endpoints(x)
    T = fmpz(10) ** D
    a = _floor(lo, e, T)
    b = _floor(hi, e, T)
    return _fmt(a, D), bool(a == b)


def rad_log2(x):
    r = x.rad()
    if r == 0:
        return float("-inf")
    m, e = r.man_exp()
    return float(int(e) + int(fmpz(m).bit_length()))


# --------------------------------------------------------------------------
# Interval Newton with precision doubling
# --------------------------------------------------------------------------


def interval_newton(f, fp, x0, prec, label):
    """Certified enclosure of the unique zero of f in a small ball.

    Floating Newton steps with precision doubling give a midpoint m; then
    with X = [m - r, m + r] the Newton operator N(X) = m - f(m)/f'(X) is
    evaluated in ball arithmetic.  If N(X) lies in the interior of X and
    0 is not in f'(X), then f has exactly one zero in X, and it lies in
    N(X) (interval Newton operator of R. E. Moore).
    """
    seq = []
    p = prec + 128
    while p > 80:
        seq.append(p)
        p = p // 2 + 40
    seq.reverse()
    ctx.prec = 80
    x = arb(x0)
    for _ in range(4):
        x = (x - f(x) / fp(x)).mid()
    for p in seq:
        ctx.prec = p
        x = (x - f(x) / fp(x)).mid()
    ctx.prec = prec
    m = x.mid()
    r = arb(2) ** (-(prec - 96))
    X = arb(m, r)
    dX = fp(X)
    if dX.contains(0):
        raise RuntimeError(label + ": derivative ball contains 0")
    Nx = m - f(m) / dX
    if not X.contains_interior(Nx):
        raise RuntimeError(label + ": interval Newton inclusion failed")
    return Nx, {"midpoint_radius_log2": -(prec - 96),
                "newton_ball_radius_log2": rad_log2(Nx),
                "inclusion_N(X)_in_interior_X": True,
                "derivative_ball_excludes_0": True}


# --------------------------------------------------------------------------
# Independent zeta(3): Amdeberhan--Zeilberger series by binary splitting
#   zeta(3) = (1/64) sum_{k>=0} (-1)^k (k!)^10 (205k^2+250k+77) / ((2k+1)!)^5
# term ratio of the hypergeometric part: -(k+1)^5 / (32 (2k+3)^5)
# --------------------------------------------------------------------------


def _bs(a, b):
    """Binary splitting on [a, b): returns P, Q, T with
    sum_{k=a}^{b-1} A(k) prod_{j=a}^{k-1} p(j)/q(j) = T / Q,  P = prod p."""
    if b - a == 1:
        k = a
        p = -fmpz(k + 1) ** 5
        q = 32 * fmpz(2 * k + 3) ** 5
        A = fmpz(205 * k * k + 250 * k + 77)
        return p, q, A * q
    m = (a + b) // 2
    P1, Q1, T1 = _bs(a, m)
    P2, Q2, T2 = _bs(m, b)
    return P1 * P2, Q1 * Q2, T1 * Q2 + P1 * T2


def zeta3_az(prec):
    # |term_N| <= A(N) 1024^(-N); choose N with 1024^(-N) A(N) < 2^(-prec-64)
    N = (prec + 64 + 64) // 10 + 2
    P, Q, T = _bs(0, N)
    # T/Q = sum_{k<N} A(k) prod_{j<k} p(j)/q(j)   (exact rational partial sum)
    ctx.prec = prec + 64
    S = arb(T) / arb(Q)
    tail = arb(205 * N * N + 250 * N + 77) * arb(2) ** (-10 * N)
    S = S + arb(0, tail)
    z = S / 64
    ctx.prec = prec
    return +z, {"terms": N, "tail_bound_log2": -10 * N + float(
        fmpz(205 * N * N + 250 * N + 77).bit_length())}


# The leaf convention above: for a single index k the partial sum is A(k)
# (empty product), and returning (p, q, A*q) makes T/Q = A(k).  Merging
# [a,m) and [m,b) gives T/Q = T1/Q1 + (P1/Q1) T2/Q2, i.e. the second block
# is multiplied by prod_{j=a}^{m-1} p(j)/q(j), which is the required weight.


# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------

MANUSCRIPT_50 = {
    "alpha_CL_deg": "112.93167025490469621261195929014436025897847010921393",
    "W1_mu1_nu1": "0.13661977236758134307553505349005744813783858296183",
    "W2_mu1_nu1": "0.15087698364770937381074949892522371428684630516813",
    "Winf_mu1_nu1": "0.21051366235301868432776943515583366338518237303085",
    "W2sq_mu1_nu1": "0.02276386419463116178229762765551222209846313595536",
    "D5": "0.18313090413989577104608117450497754779751847095684",
    "W1_rho_a": "0.50514404235910598133179797642641412865198380448805",
    "W2_rho_a": "0.58208553300559051545604864104846029987534647497147",
    "W1_rho_b": "0.51984182914554522828164803877243627920338910304217",
    "W2_rho_b": "0.59543909938728900171380288132459176482717017334995",
}

META = {
    "u_star": ("(293)", "u_* > 0 with u_* tanh u_* = 1 (OEIS A085984)"),
    "lambda_CL": ("(294)", "lambda_CL = u_*/cosh u_* = 1/sinh u_* = sqrt(u_*^2 - 1) (OEIS A033259)"),
    "alpha_CL_rad": ("(295)", "alpha_CL = 2 arccot(lambda_CL), radians"),
    "alpha_CL_deg": ("(296)", "alpha_CL in degrees"),
    "Lstar_over_a": ("(300)", "L_*/a = 2 u_* r_E(2 i u_*) = 2/lambda_CL"),
    "W1_mu1_nu1": ("(365)", "W_1(mu_1,nu_1) = 2/pi - 1/2"),
    "W2_mu1_nu1": ("(366)", "W_2(mu_1,nu_1) = sqrt(5/6 - 8/pi^2)"),
    "Winf_mu1_nu1": ("(367)", "W_inf(mu_1,nu_1) = sqrt(1-q^2) - q arccos q, q = 2/pi"),
    "W2sq_mu1_nu1": ("(368)", "W_2(mu_1,nu_1)^2 = 5/6 - 8/pi^2"),
    "D5": ("(369)", "D_5 = (62/75) zeta(3) - 8/pi^2"),
    "W1_rho_a": ("(411)", "W_1(rho_a,nu_a) = 1 - tanh(a/2)/a, a = 1/sqrt 8"),
    "W2_rho_a": ("(412)", "W_2(rho_a,nu_a) = sqrt(1 - 2 L(a)/a), L(x) = coth x - 1/x"),
    "W1_rho_b": ("(413)", "W_1(rho_b,nu_b) = 1 - tanh(b/2)/b, b = 1/sqrt 2"),
    "W2_rho_b": ("(414)", "W_2(rho_b,nu_b) = sqrt(1 - 2 L(b)/b)"),
}


def route_A(prec, notes):
    out = {}
    t0 = time.time()
    f = lambda u: u * u.sinh() - u.cosh()
    fp = lambda u: u * u.cosh()
    u, info = interval_newton(f, fp, 1.1996786402577338, prec, "A:u_*")
    notes["A_u_star_newton"] = info
    ctx.prec = prec
    out["u_star"] = u
    lam = 1 / u.sinh()
    out["lambda_CL"] = lam
    pi = arb.pi()
    alpha = 2 * (1 / lam).atan()
    out["alpha_CL_rad"] = alpha
    out["alpha_CL_deg"] = alpha * 180 / pi
    out["Lstar_over_a"] = 2 / lam
    q = 2 / pi
    W1 = q - arb(1) / 2
    W2sq = arb(5) / 6 - 2 * q * q
    out["W1_mu1_nu1"] = W1
    out["W2_mu1_nu1"] = W2sq.sqrt()
    out["Winf_mu1_nu1"] = (1 - q * q).sqrt() - q * q.acos()
    out["W2sq_mu1_nu1"] = W2sq
    out["D5"] = arb(62) / 75 * arb(3).zeta() - 8 / (pi * pi)
    for tag, x in (("a", 1 / arb(8).sqrt()), ("b", 1 / arb(2).sqrt())):
        L = x.coth() - 1 / x
        out["W1_rho_" + tag] = 1 - (x / 2).tanh() / x
        out["W2_rho_" + tag] = (1 - 2 * L / x).sqrt()
    notes["A_seconds"] = round(time.time() - t0, 2)
    # consistency checks of the manuscript's identities inside route A
    checks = {
        "lambda=u/cosh u": (u / u.cosh()).overlaps(lam),
        "lambda=sqrt(u^2-1)": ((u * u - 1).sqrt()).overlaps(lam),
        "u tanh u = 1": (u * u.tanh()).overlaps(arb(1)),
        "Lstar = 2 u r_E(2iu) = 2 sinh u": (2 * u.sinh()).overlaps(2 / lam),
    }
    notes["A_identity_checks"] = checks
    return out


def route_B(prec, notes):
    out = {}
    t0 = time.time()

    def g(l):
        s = (1 + l * l).sqrt()
        return l * s.exp() - 1 - s

    def gp(l):
        s = (1 + l * l).sqrt()
        return s.exp() * (1 + l * l / s) - l / s

    lam, info = interval_newton(g, gp, 0.6627434193491816, prec, "B:lambda_CL")
    notes["B_lambda_newton"] = info
    ctx.prec = prec
    out["lambda_CL"] = lam
    u = (1 + lam * lam).sqrt()
    out["u_star"] = u
    pi = 16 * (arb(1) / 5).atan() - 4 * (arb(1) / 239).atan()
    alpha = pi - 2 * lam.atan()
    out["alpha_CL_rad"] = alpha
    out["alpha_CL_deg"] = 180 - 360 * lam.atan() / pi
    out["Lstar_over_a"] = 2 * u.sinh()
    q = 2 / pi
    W1 = q - arb(1) / 2
    W2sq = arb(1) / 3 - 2 * W1 - 2 * W1 * W1
    out["W1_mu1_nu1"] = W1
    out["W2sq_mu1_nu1"] = W2sq
    out["W2_mu1_nu1"] = W2sq.sqrt()
    s = (1 - q * q).sqrt()
    out["Winf_mu1_nu1"] = s - q * (s / q).atan()
    t1 = time.time()
    z3, zinfo = zeta3_az(prec)
    zinfo["seconds"] = round(time.time() - t1, 2)
    notes["B_zeta3_AZ"] = zinfo
    ctx.prec = prec
    out["D5"] = arb(62) / 75 * z3 - 2 * q * q
    r2 = arb(2).sqrt()
    for tag, x in (("a", r2 / 4), ("b", r2 / 2)):
        e = x.exp()
        ei = 1 / e
        sh = (e - ei) / 2
        ch = (e + ei) / 2
        out["W1_rho_" + tag] = 1 - (ch - 1) / (x * sh)
        out["W2_rho_" + tag] = (1 - 2 * (x * ch - sh) / (x * x * sh)).sqrt()
    notes["B_seconds"] = round(time.time() - t0, 2)
    notes["B_zeta3_overlaps_Arb_zeta3"] = z3.overlaps(arb(3).zeta())
    notes["B_Machin_pi_overlaps_Arb_pi"] = pi.overlaps(arb.pi())
    return out


ORDER = ["u_star", "lambda_CL", "alpha_CL_rad", "alpha_CL_deg", "Lstar_over_a",
         "W1_mu1_nu1", "W2_mu1_nu1", "Winf_mu1_nu1", "W2sq_mu1_nu1", "D5",
         "W1_rho_a", "W2_rho_a", "W1_rho_b", "W2_rho_b"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prec", type=int, default=3_600_000)
    ap.add_argument("--digits", type=int, default=1_000_001)
    ap.add_argument("--out", default="out")
    args = ap.parse_args()
    prec, D = args.prec, args.digits
    os.makedirs(os.path.join(args.out, "digits"), exist_ok=True)
    notes = {}
    T0 = time.time()
    A = route_A(prec, notes)
    ctx.prec = prec
    B = route_B(prec, notes)
    ctx.prec = prec
    results = {}
    all_ok = True
    for key in ORDER:
        eq, formula = META[key]
        xa, xb = A[key], B[key]
        sa, ca = certified_rounding(xa, D)
        sb, cb = certified_rounding(xb, D)
        tr, ct = certified_truncation(xa, D + 10)
        s50a, c50a = certified_rounding(xa, 50)
        rec = {
            "equation": eq,
            "formula": formula,
            "route_A_radius_log2": rad_log2(xa),
            "route_B_radius_log2": rad_log2(xb),
            "balls_overlap": bool(xa.overlaps(xb)),
            "rounding_certified_A": ca,
            "rounding_certified_B": cb,
            "A_equals_B_all_digits": sa == sb,
            "truncation_to_D+10_certified": ct,
            "guard_digits_D+1..D+10_truncated": tr[-10:],
            "decimals": D,
            "integer_part": sa.split(".")[0],
            "first_60_decimals": sa.split(".")[1][:60],
            "last_20_decimals": sa[-20:],
            "rounded_50_certified": s50a if c50a else None,
        }
        if key in MANUSCRIPT_50:
            rec["manuscript_50"] = MANUSCRIPT_50[key]
            rec["manuscript_50_matches"] = (c50a and s50a == MANUSCRIPT_50[key])
        ok = ca and cb and sa == sb and rec["balls_overlap"]
        if key in MANUSCRIPT_50:
            ok = ok and rec["manuscript_50_matches"]
        rec["ok"] = ok
        all_ok = all_ok and ok
        fn = os.path.join(args.out, "digits", key + ".txt")
        with open(fn, "w") as fh:
            fh.write(sa + "\n")
        with open(fn, "rb") as fh:
            rec["file"] = "digits/" + key + ".txt"
            rec["sha256"] = hashlib.sha256(fh.read()).hexdigest()
        results[key] = rec
        print("%-14s %-6s ok=%s  r_A=2^%.0f r_B=2^%.0f  %s..." % (
            key, eq, ok, rec["route_A_radius_log2"], rec["route_B_radius_log2"],
            sa[:30]), flush=True)
    log = {
        "manuscript": "M15 (QUARTER package, 22 Nov 2026)",
        "precision_bits": prec,
        "decimals": D,
        "python_flint": flint.__version__,
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "total_seconds": round(time.time() - T0, 2),
        "notes": notes,
        "results": results,
        "ALL_OK": all_ok,
    }
    with open(os.path.join(args.out, "certification_log.json"), "w") as fh:
        json.dump(log, fh, indent=1, default=str)
    print("ALL_OK", all_ok, "seconds", log["total_seconds"])
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
