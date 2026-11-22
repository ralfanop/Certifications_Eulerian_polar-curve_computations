#!/usr/bin/env python3
"""M12 Table 1 at 1000000 working bits: strict rounding of the 25 printed cells
to 290000 significant digits and to 290000 fixed decimal places.

Inputs (run 44782807031, which passed TABLE 100000 SUCCESS 25 checks): the
certified roots X0 of m12-table-100000.json (about 100000 relative bits), the
pre-stage balls W of m12-pre-<row>.json (about 57700 bits), and the enclosures
D of H' on W of m12-deriv-<row>.json (about 42000 relative bits).

Every step is an interval Newton step on the fixed ball W with the fixed
enclosure D: for an exact point m in W and an enclosure of H(m),
    root in  m - (H(m) - t)/D,
by the mean value theorem, since the root and m lie in W and D contains H' on
W.  The enclosure is intersected with the previous one.  Its width is about
|m - root| times 2^(-42000) plus the error of H(m), so the points m are made
accurate first: m_0 is the midpoint of X0, m_1 the chord point with the
midpoint of D, and m_{k+1} the secant point of (m_{k-1}, m_k) (its accuracy
roughly adds those of m_k and m_{k-1}).  The points are not part of the proof;
only the enclosures are.  H(m_k) is evaluated at the precision p_k that the
next point needs, and at P once m_k is accurate to P - 42000 bits, after which
the enclosure has about P - 100 bits.

H(m) is the complete periodic-strip rule of #418 with the tail bound, split
into shards of interior nodes as in #429; no derivative integral is evaluated
at high precision.

Stages:
  r<k> ROW --index I   shard I of H(m_k)
  x<k> ROW             Newton step k and the next point
  certify              F(t) for the five rows and the 25 printed cells
  matrix SPEC          GitHub matrix for [stage, row] or [stage, row, start, stop]
  smoke                whole pipeline at 16384 bits with two shards
In the smoke test W is X0 widened to about P/10 bits and D is computed on it
by m12_profile_interval_newton.integrals.
"""
import argparse
import json
import math
import os
import resource
import time
from fractions import Fraction as Q
from pathlib import Path

import million_decimal_common as common   # python-flint 0.9.0, no int-str limit
from flint import arb, acb, fmpq, fmpz, ctx
from m12_profile_interval_newton import A, integrals, printed_check
from m12_profile_interval_newton import ROWS as PROFILES
from m12_periodic_shards import plan, node, bounds
from m12_table_final_errors import ROWS

P = int(os.environ.get('M12_MILLION_BITS', '1000000'))
assert P in (16384, 1000000)
SMOKE = P != 1000000
DIGITS = 290000 if not SMOKE else 4600
B0 = P // 10
SLUG = {'1/4': 'quarter', '1/2': 'half', '1': 'one', '2': 'two', '4': 'four'}
ROWNAMES = list(SLUG)
SOURCE_BITS = 100000
SOURCE_PRE = SOURCE_BITS // 2 + 256

# Slowest node cost (seconds) measured by the probe run 44813261716, made
# monotone, with a 10% margin; shards of at most 4.5 hours.
COST = [(100000, 0.030), (200000, 0.165), (400000, 0.447), (800000, 1.15), (1000000, 1.15)]
BUDGET = 16200


def node_cost(p):
    for (p0, c0), (p1, c1) in zip(COST, COST[1:]):
        if p <= p1:
            p = max(p, p0)
            return 1.1 * math.exp(math.log(c0) + (math.log(c1) - math.log(c0)) *
                                  (math.log(p) - math.log(p0)) / (math.log(p1) - math.log(p0)))
    raise ValueError(p)


def shard_count(p, N):
    if SMOKE:
        return 2
    return max(1, math.ceil((N // 4 - 1) * node_cost(p) / BUDGET))


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
    d = json.loads((folder / 'm12-table-100000.json').read_text())
    assert d['working_bits'] == SOURCE_BITS and len(d['checks']) == 25
    lo, hi = d['roots'][row]['root_lower'], d['roots'][row]['root_upper']
    ctx.prec = P + 512
    X = dyadic_ball(lo, hi)
    if SMOKE:
        ctx.prec = B0
        Y = arb(fmpq(lo)).union(arb(fmpq(hi)))
        lo, hi = endpoints(Y)
        ctx.prec = P + 512
        X = dyadic_ball(lo, hi)
    else:
        assert X.rel_accuracy_bits() >= SOURCE_BITS - 100
    return X


def ball_and_derivative(row, folder):
    """W, an enclosure D of H' on W, and D's relative bits.  X0 lies in W."""
    X = x0(row, folder)
    if SMOKE:
        W = X
        goal = W.rel_accuracy_bits() - 48
        ctx.prec = goal + 96
        D = integrals(W, True, goal=goal)
    else:
        d = json.loads((folder / f'm12-pre-{SLUG[row]}.json').read_text())
        assert d['row'] == row and d['working_bits'] == SOURCE_BITS and d['pre_bits'] == SOURCE_PRE
        ctx.prec = P + 512
        W = dyadic_ball(d['root_lower'], d['root_upper'], SOURCE_PRE)
        e = json.loads((folder / f'm12-deriv-{SLUG[row]}.json').read_text())
        assert e['row'] == row and e['working_bits'] == SOURCE_BITS
        assert (e['root_lower'], e['root_upper']) == endpoints(W)
        D = dyadic_ball(e['lower'], e['upper'])
    assert D.is_finite() and D > 0
    assert W.contains(X)
    return W, D, D.rel_accuracy_bits() - 16


def target(row):
    return common.exact(Q(row))


def evaluation_bits(a, a_prev, dW, k):
    """Precision for H(m_k), from the estimated accuracies of m_k and m_{k-1}."""
    if a >= P - dW + 128:
        return P
    gain = dW if k == 0 else a_prev
    return min(P, min(a + gain, P - dW + 1024) + 128)


def point(k, row, folder):
    """m_k, p_k and the estimated accuracies (a_k, a_{k-1})."""
    if k == 0:
        X = x0(row, folder)
        _, _, dW = ball_and_derivative(row, folder)
        a = X.rel_accuracy_bits()
        ctx.prec = P + 512
        return X.mid(), evaluation_bits(a, None, dW, 0), a, None
    d = json.loads((folder / f'm12m-x{k - 1}-{SLUG[row]}.json').read_text())
    assert d['row'] == row and d['working_bits'] == P and d['step'] == k - 1 and not d['final']
    ctx.prec = P + 512
    m = dyadic_ball(d['next_point'], d['next_point'])
    return m, d['next_bits'], d['next_estimate'], d['estimate']


def stage_r(k, row, i, folder):
    start = time.monotonic()
    S, p, _, _ = point(k, row, folder)
    assert S.rad() == 0 and S > 0
    N, _ = plan(S, p)                  # ctx.prec = p
    m = N // 4
    K = shard_count(p, N)
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


def residual(k, row, folder):
    S, p, a, a_prev = point(k, row, folder)
    N, tail = plan(S, p)
    m = N // 4
    K = shard_count(p, N)
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
    return S, H, p, a, a_prev


def previous(k, row, folder):
    """The enclosure Z_{k-1} (X0 for k = 0) and, for k >= 1, m_{k-1} and H(m_{k-1})."""
    if k == 0:
        return x0(row, folder), None, None
    d = json.loads((folder / f'm12m-x{k - 1}-{SLUG[row]}.json').read_text())
    assert d['row'] == row and d['working_bits'] == P and d['step'] == k - 1
    ctx.prec = P + 512
    Z = dyadic_ball(d['root_lower'], d['root_upper'], d['relative_bits'] - 4)
    return Z, dyadic_ball(d['point'], d['point']), dyadic_ball(d['H_mid'], d['H_mid'])


def stage_x(k, row, folder):
    start = time.monotonic()
    W, D, dW = ball_and_derivative(row, folder)
    Zp, m_prev, H_prev = previous(k, row, folder)
    S, H, p, a, a_prev = residual(k, row, folder)
    assert W.contains(S), 'the point must lie in W'
    ctx.prec = p + 64
    t = target(row)
    Y = S - (H - t) / D
    assert Y.is_finite()
    Z = Zp.intersection(Y)
    b = Zp.rel_accuracy_bits()
    assert Z.rel_accuracy_bits() > b, ('no contraction', k, row, b, Z.rel_accuracy_bits())
    rl, ru = endpoints(Z)
    Hm = H.mid()
    data = dict(row=row, working_bits=P, step=k, bits=p, derivative_bits=dW, previous_bits=b,
                relative_bits=Z.rel_accuracy_bits(), root_lower=rl, root_upper=ru,
                point=endpoints(S)[0], H_mid=endpoints(Hm)[0], estimate=a,
                final=Z.rel_accuracy_bits() >= P - 100)
    if data['final']:
        ctx.prec = P
        F = A(acb(Z)).real ** 2 / 4
        assert F.rel_accuracy_bits() >= P - 120, ('F accuracy', F.rel_accuracy_bits())
        printed_check(row, F)
        data['F_relative_bits'] = F.rel_accuracy_bits()
    else:
        if k == 0:
            slope = D.mid()
            nxt = min(a + dW, p - 100)
        else:
            slope = (Hm - H_prev) / (S - m_prev)
            nxt = min(a + a_prev, p - 100)
        q = evaluation_bits(nxt, a, dW, k + 1)
        ctx.prec = max(p, q) + 64
        m_next = (S - (Hm - t) / slope).mid()
        ctx.prec = q + 64
        m_next = (m_next * 1).mid()
        assert m_next > 0 and W.contains(m_next), 'the next point must lie in W'
        data.update(next_point=endpoints(m_next)[0], next_bits=q, next_estimate=nxt)
    data['elapsed_seconds'] = time.monotonic() - start
    write(f'm12m-x{k}-{SLUG[row]}.json', data)
    print('STEP PASS', f'x{k}', row, 'bits', b, '->', Z.rel_accuracy_bits(), 'evaluation bits', p,
          'point estimate', a, 'final' if data['final'] else f'next bits {data["next_bits"]}', flush=True)


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
        finals = []
        for f in sorted(folder.glob(f'm12m-x*-{SLUG[row]}.json')):
            d = json.loads(f.read_text())
            if d['row'] == row and d['working_bits'] == P and d['final']:
                finals.append(d)
        assert len(finals) == 1, (row, len(finals))
        d = finals[0]
        ctx.prec = P + 512
        Z = dyadic_ball(d['root_lower'], d['root_upper'], d['relative_bits'] - 4)
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


def matrix(spec, folder):
    """GitHub matrix for [stage, row] (every shard) or [stage, row, start, stop]."""
    out = []
    for item in json.loads(spec):
        stage, row = item[:2]
        assert stage[0] == 'r'
        S, p, _, _ = point(int(stage[1:]), row, folder)
        N, _ = plan(S, p)
        K = shard_count(p, N)
        start, stop = item[2:] if len(item) == 4 else (0, K)
        assert 0 <= start < stop <= K
        out += [dict(stage=stage, row=row, slug=SLUG[row], index=i, bits=p, shards=K)
                for i in range(start, stop)]
    assert len({(d['stage'], d['row'], d['index']) for d in out}) == len(out)
    assert 0 < len(out) <= 256, len(out)
    return out


def smoke(folder):
    for row in ROWNAMES:
        k = 0
        while True:
            for i in range(2):
                stage_r(k, row, i, folder)
            stage_x(k, row, folder)
            d = json.loads((folder / f'm12m-x{k}-{SLUG[row]}.json').read_text())
            if d['final']:
                break
            k += 1
            assert k < 12
    stage_certify(folder)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('stage')
    ap.add_argument('row', nargs='?')
    ap.add_argument('--index', type=int, default=0)
    ap.add_argument('--folder', type=Path, default=Path('.'))
    ns = ap.parse_args()
    s = ns.stage
    if s == 'matrix':
        print(json.dumps(matrix(ns.row, ns.folder)))
    elif s == 'smoke':
        assert SMOKE
        smoke(ns.folder)
    elif s == 'certify':
        stage_certify(ns.folder)
    else:
        assert ns.row in SLUG and s[0] in 'rx' and s[1:].isdigit()
        if s[0] == 'r':
            stage_r(int(s[1:]), ns.row, ns.index, ns.folder)
        else:
            stage_x(int(s[1:]), ns.row, ns.folder)
