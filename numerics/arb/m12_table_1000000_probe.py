#!/usr/bin/env python3
"""Timing probe for Table 1 at 1000000 working bits. Certifies nothing.

Measures, on a hosted runner, (a) the cost of one node of the periodic-strip
residual of #418 and the node count of its plan at 200000-1000000 bits, and
(b) the cost of one piece of the derivative integral of
m12_profile_interval_newton.integrals on [i/64, (i+1)/64] at 100000 bits.
The points S are the 100000-bit pre-root midpoints rounded to 30 digits; they
only fix the plan, which does not depend on the last digits of S.
"""
import sys
import time
from flint import arb, acb, ctx
from m12_periodic_shards import plan, node
from m12_profile_interval_newton import A, exprel

S_ROW = {'1/4': '3.965653819', '1/2': '6.541712699', '1': '12.83188244',
         '2': '31.47317894', '4': '92.87438233'}


def nodes(row):
    for bits in (200000, 400000, 600000, 800000, 1000000):
        ctx.prec = bits
        S = arb(S_ROW[row])
        t = time.monotonic()
        N, _ = plan(S, bits)
        tp = time.monotonic() - t
        m = N // 4
        aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
        step = arb.pi() / (2 * m)
        node(S, aS, step, 1)                      # warm-up (constants)
        times = []
        for j in (m // 5, m // 2, 4 * m // 5):
            t = time.monotonic()
            x = node(S, aS, step, j)
            times.append(time.monotonic() - t)
            assert x.is_finite() and x.rel_accuracy_bits() >= bits - 100
        print('NODE PROBE', row, 'bits', bits, 'N', N, 'interior', m - 1, 'plan seconds', round(tp, 2),
              'node seconds', ' '.join(f'{x:.4f}' for x in times), flush=True)


def piece(row, i, k, goal):
    ctx.prec = goal + 96
    Sc = acb(arb(S_ROW[row]))
    a = A(Sc)
    es = Sc.expm1()
    half = Sc / 2

    def low(u, analytic):
        s = half * u
        return half / (a * a - A(s) ** 2).sqrt(analytic=analytic)

    def high(u, analytic):
        s = Sc - half * u * u
        delta = half * u * u
        B = 1 / (Sc * s) - s.exp() * exprel(delta) / (es * s.expm1())
        return Sc / (half * B * (a + A(s))).sqrt(analytic=analytic)
    tol = arb(2) ** (-goal)
    for name, f in (('low', low), ('high', high)):
        t = time.monotonic()
        v = acb.integral(f, arb(i) / k, arb(i + 1) / k, rel_tol=tol, abs_tol=tol, eval_limit=2000000)
        print('DERIV PIECE PROBE', row, name, f'{i}/{k}', 'goal', goal, 'seconds', round(time.monotonic() - t, 1),
              'relative bits', v.real.rel_accuracy_bits(), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'nodes':
        nodes(sys.argv[2])
    else:
        for row, i in (('1', 0), ('1', 32), ('1', 63), ('4', 0), ('4', 32)):
            piece(row, i, 64, 100000)
