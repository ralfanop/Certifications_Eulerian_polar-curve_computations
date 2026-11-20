#!/usr/bin/env python3
"""M12 Table 1 at 1000000 working bits: strict rounding of the 25 printed cells
to 290000 significant digits and to 290000 fixed decimal places.

The methods are those of m12_table_100000.py: the interval Newton method of
#390 (m12_profile_interval_newton), the periodic-strip residual of #418 with
the certified sharding of #429 (m12_periodic_shards), and the full-precision
Lanczos endpoints of run 44313014167 (#386).  The starting balls X0 are the
certified roots of the 100000-bit run (m12-table-100000.json, about 100000
relative bits).  Writing b_k for the relative bits of X_k:

  step 1   derivative D0 on X0 to b0-48 bits, residual at 2 b0 + 96 bits  -> X1
  step 2   derivative D1 on X1 to b1-48 bits, residual at 0.4 P bits      -> X2
  step 3   D1 again, residual at 0.6 P bits                               -> X3
  step 4   D1 again, residual at 0.8 P bits                               -> X4
  step 5   derivative D2 on X4 to P-b4+160 bits, residual at P bits       -> Z

Steps 3 and 4 are interval Newton steps with the enclosure D1 of H' on X1;
they are valid because X3 and X2 lie in X1, which is asserted.  Every residual
is the complete periodic-strip rule split into shards of interior nodes, and
every derivative is the integral of m12_profile_interval_newton.integrals
(derivative=True) split into the pieces [i/K, (i+1)/K] of [0, 1], K a power
of 2, so that the pieces have exact dyadic endpoints.

Stages:
  d0|d1|d2 ROW --index I   derivative piece I
  r1..r5 ROW --index I     residual shard I
  x1..x5 ROW               Newton step (combines the pieces and the shards)
  certify                  F(t) for the five rows and the 25 printed cells
  matrix SPEC              GitHub matrix for a list of [stage, row] pairs
  smoke                    whole pipeline at 16384 bits with two shards
"""
import argparse
import json
import os
import resource
import time
from fractions import Fraction as Q
from pathlib import Path

import million_decimal_common as common   # python-flint 0.9.0, no int-str limit
from flint import arb, acb, fmpq, fmpz, ctx
from m12_profile_interval_newton import A, exprel, integrals, printed_check
from m12_profile_interval_newton import ROWS as PROFILES
from m12_periodic_shards import plan, node, bounds
from m12_table_final_errors import ROWS

P = int(os.environ.get('M12_MILLION_BITS', '1000000'))
assert P in (16384, 1000000)
SMOKE = P != 1000000
DIGITS = 290000 if not SMOKE else 4600
B0 = P // 10
LADDER = {2: 4 * P // 10, 3: 6 * P // 10, 4: 8 * P // 10, 5: P}
SLUG = {'1/4': 'quarter', '1/2': 'half', '1': 'one', '2': 'two', '4': 'four'}
ROWNAMES = list(SLUG)

# Shards of interior nodes per residual (about 4.5 hours each at the node
# costs measured by the probe run 44813261716), and derivative pieces per
# derivative (powers of 2).
SHARDS = {
    'r1': {'1/4': 1, '1/2': 2, '1': 3, '2': 5, '4': 9},
    'r2': {'1/4': 3, '1/2': 6, '1': 11, '2': 22, '4': 44},
    'r3': {'1/4': 7, '1/2': 13, '1': 26, '2': 52, '4': 103},
    'r4': {'1/4': 15, '1/2': 30, '1': 59, '2': 117, '4': 233},
    'r5': {'1/4': 21, '1/2': 41, '1': 82, '2': 163, '4': 325},
}
PIECES = {
    'd0': {'1/4': 2, '1/2': 2, '1': 4, '2': 8, '4': 16},
    'd1': {'1/4': 8, '1/2': 16, '1': 32, '2': 64, '4': 128},
    'd2': {'1/4': 8, '1/2': 16, '1': 32, '2': 64, '4': 128},
}
if SMOKE:
    SHARDS = {k: {r: 2 for r in ROWNAMES} for k in SHARDS}
    PIECES = {k: {r: 2 for r in ROWNAMES} for k in PIECES}
for table in PIECES.values():
    for K in table.values():
        assert K > 0 and K & (K - 1) == 0

root = Path('sources')


def dyadic_ball(l, u, bits=None):
    lo, hi = fmpq(l), fmpq(u)
    assert 0 < lo <= hi
    for q in (lo, hi):
        assert q.q > 0 and (q.q & (q.q - 1)) == 0
    x = arb(lo).union(arb(hi))
    assert x.lower().fmpq() <= lo and hi <= x.upper().fmpq()
    if bits is not None:
        assert x.rel_accuracy_bits() >= bits, (x.rel_accuracy_bits(), bits)
    return x


def endpoints(x):
    # arb.lower/upper round to the working precision: read exact endpoints at a
    # precision above that of every ball handled here.
    p = ctx.prec
    ctx.prec = P + 4096
    try:
        return str(x.lower().fmpq()), str(x.upper().fmpq())
    finally:
        ctx.prec = p


def write(name, data):
    data['peak_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    Path(name).write_text(json.dumps(data) + '\n')


def x0(row, folder):
    """Certified root of the 100000-bit run; in the smoke test it is widened to
    about P/10 bits, so that the smoke test follows the same ladder."""
    table = folder / 'm12-table-100000.json'
    if table.exists():
        d = json.loads(table.read_text())
        assert d['working_bits'] == 100000 and len(d['checks']) == 25
        lo, hi = d['roots'][row]['root_lower'], d['roots'][row]['root_upper']
    else:
        assert SMOKE, 'the 1000000-bit run starts from m12-table-100000.json'
        d = json.loads((folder / f'm12-pre-{SLUG[row]}.json').read_text())
        assert d['row'] == row and d['working_bits'] == 100000
        lo, hi = d['root_lower'], d['root_upper']
    ctx.prec = P + 512
    X = dyadic_ball(lo, hi)
    if X.rel_accuracy_bits() > B0 + 64:
        ctx.prec = B0
        Y = arb(fmpq(lo)).union(arb(fmpq(hi)))
        lo, hi = endpoints(Y)
        ctx.prec = P + 512
        X = dyadic_ball(lo, hi)
    assert X > 0 and X.rel_accuracy_bits() >= B0 - 512, X.rel_accuracy_bits()
    return X


def xk(k, row, folder):
    if k == 0:
        return x0(row, folder)
    d = json.loads((folder / f'm12m-x{k}-{SLUG[row]}.json').read_text())
    assert d['row'] == row and d['working_bits'] == P and d['step'] == k
    ctx.prec = P + 512
    return dyadic_ball(d['root_lower'], d['root_upper'], d['relative_bits'] - 4)


DERIV_BALL = {0: 0, 1: 1, 2: 4}          # derivative k is taken on X_{DERIV_BALL[k]}
RESID_BALL = {1: 0, 2: 1, 3: 2, 4: 3, 5: 4}


def deriv_goal(k, b):
    return b - 48 if k in (0, 1) else P - b + 160


def integrands(X):
    """The integrands of m12_profile_interval_newton.integrals with
    derivative=True, at the current precision."""
    Sc = acb(X)
    a = A(Sc)
    es = Sc.expm1()
    half = Sc / 2

    def low(u, analytic):
        s = half * u
        r = (a * a - A(s) ** 2).sqrt(analytic=analytic)
        return half / r

    def high(u, analytic):
        s = Sc - half * u * u
        delta = half * u * u
        B = 1 / (Sc * s) - s.exp() * exprel(delta) / (es * s.expm1())
        r = (half * B * (a + A(s))).sqrt(analytic=analytic)
        return Sc / r
    return low, high


def stage_d(k, row, i, folder):
    start = time.monotonic()
    X = xk(DERIV_BALL[k], row, folder)
    b = X.rel_accuracy_bits()
    goal = deriv_goal(k, b)
    K = PIECES[f'd{k}'][row]
    assert 0 <= i < K
    ctx.prec = goal + 96
    tol = arb(2) ** (-goal)
    v = acb(0)
    for f in integrands(X):
        v += acb.integral(f, arb(i) / K, arb(i + 1) / K, rel_tol=tol, abs_tol=tol, eval_limit=2000000)
    assert v.is_finite() and v.imag.contains(0) and v.real > 0, ('piece', k, row, i)
    lo, hi = endpoints(v.real)
    rl, ru = endpoints(X)
    write(f'm12m-d{k}-{SLUG[row]}-{i}.json', dict(
        row=row, working_bits=P, derivative=k, goal_bits=goal, pieces=K, index=i,
        root_lower=rl, root_upper=ru, lower=lo, upper=hi,
        relative_bits=v.real.rel_accuracy_bits(), elapsed_seconds=time.monotonic() - start))
    print('PIECE PASS', f'd{k}', row, f'{i}/{K}', 'goal', goal, 'relative bits',
          v.real.rel_accuracy_bits(), 'seconds', time.monotonic() - start, flush=True)


def derivative(k, row, X, folder):
    b = X.rel_accuracy_bits()
    goal = deriv_goal(k, b)
    K = PIECES[f'd{k}'][row]
    rl, ru = endpoints(X)
    ctx.prec = goal + 96
    total = arb(0)
    for i in range(K):
        d = json.loads((folder / f'm12m-d{k}-{SLUG[row]}-{i}.json').read_text())
        assert (d['row'], d['working_bits'], d['derivative'], d['goal_bits'], d['pieces'], d['index']) == \
               (row, P, k, goal, K, i)
        assert (d['root_lower'], d['root_upper']) == (rl, ru)
        total += dyadic_ball(d['lower'], d['upper'])
    Sc = acb(X)
    a = A(Sc)
    es = Sc.expm1()
    aprime = 1 / (Sc * Sc) - Sc.exp() / (es * es)
    D = acb(total) / arb.pi() * a * aprime
    assert D.imag.contains(0) and D.real > 0
    D = D.real
    if k in (0, 1):
        assert D.rel_accuracy_bits() >= b - 100, ('derivative accuracy', k, D.rel_accuracy_bits(), b)
    else:
        assert D.rel_accuracy_bits() >= goal - 64, ('derivative accuracy', k, D.rel_accuracy_bits(), goal)
    if SMOKE:
        assert D.overlaps(integrals(X, True, goal=goal)), 'pieces disagree with the unsplit integral'
    return D, goal


def resid_bits(k, b):
    return max(384, 2 * b + 96) if k == 1 else LADDER[k]


def stage_r(k, row, i, folder):
    start = time.monotonic()
    X = xk(RESID_BALL[k], row, folder)
    b = X.rel_accuracy_bits()
    p = resid_bits(k, b)
    assert p > b
    S = X.mid()
    assert S.rad() == 0
    N, _ = plan(S, p)                  # ctx.prec = p
    m = N // 4
    K = SHARDS[f'r{k}'][row]
    assert 0 <= i < K
    lo, hi = bounds(m, i, K)
    aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
    step = arb.pi() / (2 * m)
    total = arb(0)
    for j in range(lo, hi):
        total += node(S, aS, step, j)
    assert total.is_finite() and total > 0
    assert total.rel_accuracy_bits() >= p - 100
    l, u = endpoints(total)
    write(f'm12m-r{k}-{SLUG[row]}-{i}.json', dict(
        row=row, working_bits=P, residual=k, bits=p, N=N, shards=K, index=i, lo=lo, hi=hi,
        midpoint=endpoints(S)[0], lower=l, upper=u, elapsed_seconds=time.monotonic() - start))
    print('SHARD PASS', f'r{k}', row, f'{i}/{K}', 'bits', p, 'nodes', hi - lo, 'of', m - 1,
          'relative bits', total.rel_accuracy_bits(), 'seconds', time.monotonic() - start, flush=True)


def residual(k, row, X, folder):
    b = X.rel_accuracy_bits()
    p = resid_bits(k, b)
    S = X.mid()
    N, tail = plan(S, p)
    m = N // 4
    K = SHARDS[f'r{k}'][row]
    aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
    total = 2 * aS / S
    end = 1
    for i in range(K):
        d = json.loads((folder / f'm12m-r{k}-{SLUG[row]}-{i}.json').read_text())
        lo, hi = bounds(m, i, K)
        assert (d['row'], d['working_bits'], d['residual'], d['bits'], d['N'], d['shards'], d['index'],
                d['lo'], d['hi']) == (row, P, k, p, N, K, i, lo, hi)
        assert d['midpoint'] == endpoints(S)[0]
        assert lo == end and hi > lo
        end = hi
        total += dyadic_ball(d['lower'], d['upper'], p - 100)
    assert end == m
    H = S * S * total / (2 * N) + arb(0, tail.upper())
    assert H.rel_accuracy_bits() >= p - 100 and H > 0
    return S, H, p


def stage_x(k, row, folder):
    start = time.monotonic()
    X = xk(k - 1, row, folder)
    b = X.rel_accuracy_bits()
    if k == 1:
        D, goal = derivative(0, row, X, folder)
    elif k in (2, 3, 4):
        X1 = xk(1, row, folder)
        assert X1.contains(X)
        D, goal = derivative(1, row, X1, folder)
    else:
        D, goal = derivative(2, row, X, folder)
    S, H, p = residual(k, row, X, folder)
    ctx.prec = p
    Y = S - (H - common.exact(Q(row))) / D
    assert Y.is_finite() and Y > 0
    Z = X.intersection(Y)
    assert Z.rel_accuracy_bits() > b, ('no contraction', k, row, b, Z.rel_accuracy_bits())
    rl, ru = endpoints(Z)
    data = dict(row=row, working_bits=P, step=k, residual_bits=p, derivative_goal_bits=goal,
                previous_bits=b, relative_bits=Z.rel_accuracy_bits(), root_lower=rl, root_upper=ru,
                elapsed_seconds=time.monotonic() - start)
    if k == 5:
        ctx.prec = P
        F = A(acb(Z)).real ** 2 / 4
        assert F.rel_accuracy_bits() >= P - 120, ('F accuracy', F.rel_accuracy_bits())
        printed_check(row, F)
        data['F_relative_bits'] = F.rel_accuracy_bits()
    write(f'm12m-x{k}-{SLUG[row]}.json', data)
    print('STEP PASS', f'x{k}', row, 'bits', b, '->', Z.rel_accuracy_bits(), 'residual bits', p,
          'derivative goal', goal, flush=True)


checks = []
scale = fmpz(10) ** DIGITS


def check(name, x, printed, unit):
    assert x > 0 and x.rel_accuracy_bits() >= P - 200, (name, x.rel_accuracy_bits())
    d = Q(printed)
    assert common.exact(d - unit / 2) < x < common.exact(d + unit / 2), name
    significant = common.rounded_significant(x)
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    a, b = 2 * lo.p * scale, 2 * hi.p * scale
    m = (a + lo.q) // (2 * lo.q)
    assert a > (2 * m - 1) * lo.q and b < (2 * m + 1) * hi.q, name
    checks.append(dict(name=name, printed=printed, relative_bits=x.rel_accuracy_bits(),
                       rounded_significant=significant, rounded_scaled_integer=str(m),
                       lower=str(lo), upper=str(hi)))
    print(f'TABLE {P} PASS', name, x.rel_accuracy_bits(), flush=True)


def stage_certify(folder):
    common.DIGITS = DIGITS
    profiles = {}
    for row in SLUG:
        Z = xk(5, row, folder)
        ctx.prec = P
        F = A(acb(Z)).real ** 2 / 4
        assert F.rel_accuracy_bits() >= P - 120, ('F accuracy', F.rel_accuracy_bits())
        printed_check(row, F)
        profiles[row] = (Z, F)
    coeffs = {}
    for M in (100, 200, 400):
        d = json.loads((root / f'm12-lanczos-{M}.json').read_text())
        assert d['M'] == M and d['working_bits'] == common.WORK
        assert set(d['values']) == {str(j) for j in (M // 4, M // 2, M, 2 * M, 4 * M)}
        ctx.prec = P
        coeffs[M] = {j: dyadic_ball(v['lower'], v['upper'], P - 10) for j, v in d['values'].items()}
    ctx.prec = P
    roots = {}
    for t, *ds in ROWS:
        Z, F = profiles[t]
        rl, ru = endpoints(Z)
        roots[t] = dict(root_lower=rl, root_upper=ru)
        check('F(' + t + ')', F, PROFILES[t], Q(1, 10 ** 7))
        for M, displayed in zip((100, 200, 400), ds[:3]):
            j = Q(t) * M
            assert j.denominator == 1
            E = coeffs[M][str(j.numerator)] - F
            check('M*E t=' + t + ' M=' + str(M), M * E, displayed, Q(1, 10 ** 6))
            if M == 400:
                check('E t=' + t + ' M=400', E, ds[3], Q(1, 10 ** 7))
    assert len(checks) == 25
    Path(f'm12-table-{P}.json').write_text(json.dumps(dict(
        working_bits=P, significant_digits=DIGITS, fixed_decimal_places=DIGITS,
        source_runs=[44313014167, 44782807031, int(os.environ.get('GITHUB_RUN_ID', '0'))],
        roots=roots, checks=checks), indent=2) + '\n')
    print(f'TABLE {P} SUCCESS', len(checks), 'checks', 'minimum relative bits',
          min(x['relative_bits'] for x in checks), flush=True)


def matrix(spec):
    """GitHub matrix for a list of [stage, row] pairs (every index of each)."""
    out = []
    for stage, row in json.loads(spec):
        K = (PIECES if stage[0] == 'd' else SHARDS)[stage][row]
        out += [dict(stage=stage, row=row, slug=SLUG[row], index=i) for i in range(K)]
    assert 0 < len(out) <= 256, len(out)
    return out


def smoke(folder):
    order = ['d0', 'r1', 'x1', 'd1', 'r2', 'x2', 'r3', 'x3', 'r4', 'x4', 'd2', 'r5', 'x5']
    for row in ROWNAMES:
        for stage in order:
            k = int(stage[1])
            if stage[0] == 'x':
                stage_x(k, row, folder)
            else:
                K = (PIECES if stage[0] == 'd' else SHARDS)[stage][row]
                for i in range(K):
                    (stage_d if stage[0] == 'd' else stage_r)(k, row, i, folder)
    stage_certify(folder)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('stage', choices=['d0', 'd1', 'd2', 'r1', 'r2', 'r3', 'r4', 'r5',
                                      'x1', 'x2', 'x3', 'x4', 'x5', 'certify', 'matrix', 'smoke'])
    ap.add_argument('row', nargs='?')
    ap.add_argument('--index', type=int, default=0)
    ap.add_argument('--folder', type=Path, default=Path('.'))
    ns = ap.parse_args()
    s = ns.stage
    if s == 'matrix':
        print(json.dumps(matrix(ns.row)))
    elif s == 'smoke':
        assert SMOKE
        smoke(ns.folder)
    elif s == 'certify':
        stage_certify(ns.folder)
    else:
        assert ns.row in SLUG
        if s[0] == 'd':
            stage_d(int(s[1]), ns.row, ns.index, ns.folder)
        elif s[0] == 'r':
            stage_r(int(s[1]), ns.row, ns.index, ns.folder)
        else:
            stage_x(int(s[1]), ns.row, ns.folder)
