"""Negative controls: the same certificate machinery must FAIL for wrong 80-place decimals."""
from fractions import Fraction as Fr
import hstar_cert as H
import mpmath as mp

def run(shift):
    H.d = Fr(H.D80) + shift
    H.L = H.d - Fr(1, 2 * 10**80); H.U = H.d + Fr(1, 2 * 10**80)
    B = H.MPBackend()
    mp.mp.dps = 140
    q = 2 / mp.pi; c = (1 + q) / 2; m = (1 - q) / 2
    hL = mp.mpf(H.L.numerator) / H.L.denominator
    rE = lambda t: 2 * mp.sin(t / 2) / t
    drE = lambda t: mp.cos(t / 2) / t - 2 * mp.sin(t / 2) / t**2
    def sysF(th, t):
        px, py = rE(th) * mp.cos(th), rE(th) * mp.sin(th)
        ex, ey = drE(th) * mp.cos(th) - rE(th) * mp.sin(th), drE(th) * mp.sin(th) + rE(th) * mp.cos(th)
        rl, drl = c + hL + m * mp.cos(t), -m * mp.sin(t)
        zx, zy = rl * mp.cos(t), rl * mp.sin(t)
        tx, ty = drl * mp.cos(t) - rl * mp.sin(t), drl * mp.sin(t) + rl * mp.cos(t)
        return [(px - zx) * tx + (py - zy) * ty, (px - zx) * ex + (py - zy) * ey]
    th0, tt0 = mp.findroot(sysF, (mp.mpf("2.1074"), mp.mpf("2.0956")))
    okL, gap = H.check_lower(B, {"theta0": mp.nstr(th0, 120), "t0": mp.nstr(tt0, 120)})
    try:
        _, cc, mm = H.consts(B); Ub = B.const(H.U)
        stack = [(0, 0)]; n = 0
        while stack:
            dep, idx = stack.pop()
            a = H.TA + (H.TB - H.TA) * Fr(idx, 2**dep); b = H.TA + (H.TB - H.TA) * Fr(idx + 1, 2**dep)
            tc, s = H.numeric_tc_s((a + b) / 2, H.U)
            ok, _, _ = H.panel_bound(B, a, b, Fr(tc), Fr(s), (cc, mm), Ub); n += 1
            if not ok:
                if dep > 170: raise RuntimeError
                stack += [(dep + 1, 2 * idx + 1), (dep + 1, 2 * idx)]
        okU = True
    except RuntimeError:
        okU = False
    print(f"shift {float(shift):+.1e}: Q(L)>L certified={okL} (gap {float(gap):+.3e}), Q(U)<U certified={okU}")

run(Fr(0))
run(Fr(-1, 10**80))   # true h_* lies above U: the upper test must fail
run(Fr(+1, 10**80))   # true h_* lies below L: the lower test must fail
