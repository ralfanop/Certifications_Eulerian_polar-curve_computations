#!/usr/bin/env python3
"""Certified 80-decimal enclosure for the V427 Hausdorff minimiser h_*.

Requires:
    python-flint==0.9.0
    mpmath==1.4.1

The proof has three parts.
(1) Lower rounding endpoint L: one supporting-line witness proves Q(L) > L.
(2) Upper endpoint U, outside theta in [1.98,2.22]: strict concavity from
    Theorem 3.13 plus two Arb endpoint/derivative checks proves that equal-angle
    pairing has distance < U.
(3) Upper endpoint U, theta in [1.98,2.22]: an adaptive dyadic cover chooses a
    boundary witness t for each theta-panel. Arb proves, by a mean-value bound
    on squared Euclidean distance, that every Eulerian point in that panel is
    within U of Omega_U.

mpmath is used only to CHOOSE witness t-values. Every inequality establishing
certification is checked with Arb. The JSON output stores all witnesses so that
verify_hstar_80.py can replay the proof using Arb alone.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import sys
import time

import mpmath as mp
import flint
from flint import arb, ctx

BITS = 768
MP_DPS = 220
MAX_DEPTH = 180
MAX_VISITED = 50000
OUTPUT = "HSTAR_80_CERTIFICATE.json"

H80_STR = "0.04929794832571833570703662300396701228024147449936041418804532388531218517828559"
PLACES = 80
A_Q = Fraction(99, 50)   # 1.98
B_Q = Fraction(111, 50)  # 2.22

# High-precision non-rigorous approximations used only as lower-witness choices.
THETA_H_WITNESS = (
    "2.10741833649705107378365290842173214527498505103722386230689419007825541342685777184788723896041224"
)
T_H_WITNESS = (
    "2.095558810492184822602937050379998040074680476019902672262391256408200896229536905128727177293133923"
)


def require(cond, msg):
    if not cond:
        raise ArithmeticError(msg)


def exact(q: Fraction):
    return arb(str(q.numerator)) / q.denominator


def qstr(q: Fraction):
    return f"{q.numerator}/{q.denominator}"


def ball_bounds(x, digits=110):
    return {
        "lower": x.lower().str(digits, radius=False),
        "upper": x.upper().str(digits, radius=False),
    }


ctx.prec = BITS
mp.mp.dps = MP_DPS

h80_q = Fraction(H80_STR)
half_ulp_q = Fraction(1, 2 * 10**PLACES)
L_q = h80_q - half_ulp_q
U_q = h80_q + half_ulp_q
L = exact(L_q)
U = exact(U_q)

pi = arb.pi()
q = 2 / pi
c = (1 + q) / 2
m = (1 - q) / 2

# mpmath constants are heuristic only.
mpi = mp.pi
mq = 2 / mpi
mc = (1 + mq) / 2
mm = (1 - mq) / 2
mU = mp.mpf(U_q.numerator) / U_q.denominator


def rA(th):
    return 2 * (th / 2).sin() / th


def rpA(th):
    return (th * (th / 2).cos() - 2 * (th / 2).sin()) / (th * th)


def radial_gap_A(th):
    return rA(th) - c - m * th.cos()


def radial_gap_prime_A(th):
    return rpA(th) + m * th.sin()


def distance_data_A(theta, t, h):
    """Squared distance to one boundary witness and d/dtheta of that square."""
    rr = rA(theta)
    rrp = rpA(theta)
    R = c + h + m * t.cos()
    ct, st = t.cos(), t.sin()
    cth, sth = theta.cos(), theta.sin()
    px, py = rr * cth, rr * sth
    zx, zy = R * ct, R * st
    dx, dy = px - zx, py - zy
    ppx, ppy = rrp * cth - rr * sth, rrp * sth + rr * cth
    d2 = dx * dx + dy * dy
    d2p = 2 * (dx * ppx + dy * ppy)
    return d2, d2p


def supporting_gap_A(theta, t, h):
    """Signed distance from p(theta) to the supporting line at Gamma_h(t), minus h."""
    rr = rA(theta)
    R = c + h + m * t.cos()
    Rp = -m * t.sin()
    ct, st = t.cos(), t.sin()
    cth, sth = theta.cos(), theta.sin()
    px, py = rr * cth, rr * sth
    zx, zy = R * ct, R * st
    # Outward normal N = R e_t - R' e_t^perp.
    Nx = R * ct + Rp * st
    Ny = R * st - Rp * ct
    normN = (R * R + Rp * Rp).sqrt()
    signed = ((px - zx) * Nx + (py - zy) * Ny) / normN
    return signed - h


def rM(th):
    return 2 * mp.sin(th / 2) / th


def rpM(th):
    return (th * mp.cos(th / 2) - 2 * mp.sin(th / 2)) / (th * th)


def nearest_witness_t(theta):
    """High-precision Newton solve for a good boundary witness; not part of proof."""
    rr = rM(theta)
    ct0, st0 = mp.cos(theta), mp.sin(theta)
    px, py = rr * ct0, rr * st0
    t = theta - mp.mpf("0.012")
    for _ in range(30):
        ct, st = mp.cos(t), mp.sin(t)
        R = mc + mU + mm * ct
        Rp = -mm * st
        Rpp = -mm * ct
        zx, zy = R * ct, R * st
        zpx, zpy = Rp * ct - R * st, Rp * st + R * ct
        zppx = (Rpp - R) * ct - 2 * Rp * st
        zppy = (Rpp - R) * st + 2 * Rp * ct
        dx, dy = px - zx, py - zy
        f = dx * zpx + dy * zpy
        fp = -(zpx * zpx + zpy * zpy) + dx * zppx + dy * zppy
        require(fp != 0, "Heuristic Newton derivative vanished")
        step = f / fp
        t -= step
        if abs(step) < mp.mpf("1e-195"):
            break
    require(0 < t < mpi, "Heuristic boundary witness left (0,pi)")
    return t


def certify_panel(lo_q, hi_q):
    mid_q = (lo_q + hi_q) / 2
    rad_q = (hi_q - lo_q) / 2
    mid_m = mp.mpf(mid_q.numerator) / mid_q.denominator
    tw = nearest_witness_t(mid_m)
    # 190 significant decimal digits is much finer than the 80-place target.
    t_text = mp.nstr(tw, 190)
    tA = arb(t_text)
    midA = exact(mid_q)
    radA = exact(rad_q).upper()
    IA = arb(midA, radA)
    d2c, _ = distance_data_A(midA, tA, U)
    _, d2pI = distance_data_A(IA, tA, U)
    mv_upper = d2c.upper() + d2pI.abs_upper() * radA
    # U is itself an Arb enclosure of the exact rational U_q.  U.lower() <= U_q,
    # hence proving mv_upper < U.lower()^2 is stronger than needed.
    Ulo = U.lower()
    target = Ulo * Ulo
    passed = mv_upper < target
    slack = target - mv_upper
    return bool(passed), t_text, mv_upper, slack


def main():
    t_start = time.time()
    print("python", sys.version.split()[0])
    print("python-flint", flint.__version__)
    print("Arb bits", BITS, "mpmath dps", MP_DPS)
    print("rounded candidate:", H80_STR)
    print("L =", qstr(L_q))
    print("U =", qstr(U_q))

    # ---- Lower endpoint: Q(L) > L via a supporting line. ----
    theta_w = arb(THETA_H_WITNESS)
    t_w = arb(T_H_WITNESS)
    lower_gap = supporting_gap_A(theta_w, t_w, L)
    require(lower_gap.lower() > 0, ("Lower endpoint witness failed", lower_gap))
    print("lower endpoint supporting gap:", lower_gap.str(40))

    # ---- Outside central interval at U: equal-angle proof. ----
    A = exact(A_Q)
    B = exact(B_Q)
    gpA = radial_gap_prime_A(A)
    gpB = radial_gap_prime_A(B)
    gA = radial_gap_A(A)
    gB = radial_gap_A(B)
    require(gpA.lower() > 0, ("g'(A) not certified positive", gpA))
    require(gpB.upper() < 0, ("g'(B) not certified negative", gpB))
    require((gA - 2 * U).upper() < 0, ("g(A) < 2U failed", gA - 2 * U))
    require((gB - 2 * U).upper() < 0, ("g(B) < 2U failed", gB - 2 * U))
    print("outside interval checks certified")

    # ---- Central interval at U: adaptive dyadic witness cover. ----
    stack = [(A_Q, B_Q, 0)]
    panels = []
    visited = 0
    max_depth = 0
    while stack:
        lo_q, hi_q, depth = stack.pop()
        visited += 1
        require(visited <= MAX_VISITED, "Exceeded MAX_VISITED; increase it or inspect proof")
        passed, t_text, mv_upper, slack = certify_panel(lo_q, hi_q)
        if passed:
            panels.append({
                "lo": qstr(lo_q),
                "hi": qstr(hi_q),
                "t": t_text,
                "depth": depth,
                "slack_lower": slack.lower().str(30, radius=False),
            })
            max_depth = max(max_depth, depth)
        else:
            require(depth < MAX_DEPTH, ("Exceeded MAX_DEPTH", qstr(lo_q), qstr(hi_q), mv_upper))
            mid_q = (lo_q + hi_q) / 2
            stack.append((mid_q, hi_q, depth + 1))
            stack.append((lo_q, mid_q, depth + 1))
        if visited % 500 == 0:
            print("visited", visited, "certified panels", len(panels), "stack", len(stack), flush=True)

    panels.sort(key=lambda z: Fraction(z["lo"]))
    # Exact coverage/no-gap check in rational arithmetic.
    require(Fraction(panels[0]["lo"]) == A_Q, "central cover does not start at A")
    require(Fraction(panels[-1]["hi"]) == B_Q, "central cover does not end at B")
    for x, y in zip(panels, panels[1:]):
        require(Fraction(x["hi"]) == Fraction(y["lo"]), "gap/overlap in central cover")

    print("central cover certified:", len(panels), "panels; max depth", max_depth)
    print("Therefore Q(U) < U, while Q(L) > L.")
    print("By Theorem 3.14 (strict decrease and unique zero), L < h_* < U.")
    print("CERTIFIED correctly rounded to 80 decimal places:")
    print("h_* ≈", H80_STR)

    report = {
        "quantity": "V427 unique planar Hausdorff minimiser h_*",
        "theorem_dependency": "Theorem 3.14: Q(h)-h is strictly decreasing and has one zero; Theorem 3.13: radial gap f-l is strictly concave.",
        "places": PLACES,
        "rounded": H80_STR,
        "rounding_cell": {"L": qstr(L_q), "U": qstr(U_q)},
        "parameters": {"arb_bits": BITS, "mpmath_dps_for_witness_selection_only": MP_DPS},
        "versions": {"python": sys.version, "python_flint": flint.__version__, "mpmath": mp.__version__},
        "lower_endpoint": {
            "theta_witness": THETA_H_WITNESS,
            "t_witness": T_H_WITNESS,
            "supporting_gap": ball_bounds(lower_gap),
            "claim": "supporting-line signed distance minus L is rigorously positive, hence Q(L)>L",
        },
        "upper_outside_central": {
            "A": qstr(A_Q), "B": qstr(B_Q),
            "gprime_A": ball_bounds(gpA), "gprime_B": ball_bounds(gpB),
            "gA_minus_2U": ball_bounds(gA - 2 * U),
            "gB_minus_2U": ball_bounds(gB - 2 * U),
            "claim": "strict concavity + derivative signs make g increasing on [0,A] and decreasing on [B,pi]; equal-angle distance is <U there",
        },
        "upper_central_cover": {
            "visited_nodes": visited,
            "panel_count": len(panels),
            "max_depth": max_depth,
            "panels": panels,
            "claim": "for each panel a fixed Gamma_U boundary witness has squared distance < U^2 by an Arb mean-value enclosure",
        },
        "conclusion": "Q(L)>L and Q(U)<U; strict decrease of Q(h)-h implies L<h_*<U, certifying the displayed 80-place rounding.",
        "elapsed_seconds": time.time() - t_start,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    Path(OUTPUT).write_text(json.dumps(report, indent=2) + "\n")
    print("wrote", OUTPUT)


if __name__ == "__main__":
    main()
