#!/usr/bin/env python3
"""M12 Table 1 at 100000 working bits: strict rounding of the 25 printed cells
to 29000 significant digits and to 29000 fixed decimal places.

Not a million-decimal certificate. The methods are those already used for Table 1:
the interval Newton refinement of #390 (m12_profile_interval_newton), the
periodic-strip quadrature of #418 and its certified sharding of #429
(m12_profile_periodic_strip, m12_periodic_shards), and the full-precision
Lanczos endpoints of run 44313014167 (#386). The only changes with respect to
m12_profile_root_10000 / m12_table_10000 are: no pilot node cap, and the last
interval Newton step is split into separate jobs (derivative enclosure and
sharded residual), because a single hosted job is limited to six hours.

Stages (the pinned workflow runs them in this order and authenticates the
intermediate artifacts):
  pre ROW          interval Newton until the root ball has >= PRE relative bits
  deriv ROW        enclosure of H' on the pre-root ball, to P-b+160 bits
  shard ROW I      node range I of K of the periodic residual H(m) at P bits,
                   m the exact dyadic midpoint of the pre-root ball
  certify          last interval Newton step, F(t) for the five rows and the
                   25 printed cells
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
from m12_profile_interval_newton import A, initial, integrals, printed_check
from m12_profile_interval_newton import ROWS as PROFILES
from m12_periodic_shards import plan, node, bounds
from m12_table_final_errors import ROWS

# The pinned workflow first runs the whole pipeline at 4096 bits with two shards
# (smoke test of every stage and of the file formats), then at 100000 bits.
P = int(os.environ.get('M12_TABLE_BITS', '100000'))
assert P in (4096, 100000)
PRE = P // 2 + 256
K = int(os.environ.get('M12_TABLE_SHARDS', '8'))
assert K in (2, 8)
DIGITS = 29000 if P == 100000 else 1150
SLUG = {'1/4': 'quarter', '1/2': 'half', '1': 'one', '2': 'two', '4': 'four'}
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


def residual(S, bits):
    """Complete periodic-strip rule of #418 at `bits` (no node cap)."""
    N, tail = plan(S, bits)            # sets ctx.prec = bits, goal = bits-48
    m = N // 4
    aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
    step = arb.pi() / (2 * m)
    total = 2 * aS / S
    for j in range(1, m):
        total += node(S, aS, step, j)
    H = S * S * total / (2 * N) + arb(0, tail.upper())
    assert H.is_finite() and H > 0
    assert H.rel_accuracy_bits() >= bits - 100, ('residual accuracy', H.rel_accuracy_bits())
    return H


def stage_pre(row):
    start = time.monotonic()
    target = common.exact(Q(row))
    ctx.prec = 256
    X = initial(row, 256)
    for _ in range(40):
        b = X.rel_accuracy_bits()
        if b >= PRE:
            break
        ctx.prec = max(128, b + 96)
        t = time.monotonic()
        D = integrals(X, True, goal=max(40, b - 48))
        dt = time.monotonic() - t
        assert D.is_finite() and D > 0
        assert D.rel_accuracy_bits() >= b - 100
        p = max(384, 2 * b + 96)
        m = X.mid()                     # exact dyadic
        t = time.monotonic()
        H = residual(m, p)
        ht = time.monotonic() - t
        ctx.prec = p
        Y = m - (H - target) / D
        assert Y.is_finite() and Y > 0
        Z = X.intersection(Y)
        assert Z.rel_accuracy_bits() > b, ('no contraction', b, Z.rel_accuracy_bits())
        X = Z
        print('PRE STEP', row, 'p', p, 'root bits', X.rel_accuracy_bits(),
              'derivative seconds', dt, 'residual seconds', ht, flush=True)
    assert X.rel_accuracy_bits() >= PRE
    lo, hi = endpoints(X)
    ctx.prec = 256
    assert initial(row, 256).overlaps(X)
    data = dict(row=row, working_bits=P, pre_bits=PRE, relative_bits=X.rel_accuracy_bits(),
                root_lower=lo, root_upper=hi, elapsed_seconds=time.monotonic() - start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(f'm12-pre-{SLUG[row]}.json').write_text(json.dumps(data) + '\n')
    print('PRE PASS', row, data['relative_bits'], 'seconds', data['elapsed_seconds'], flush=True)


def load_pre(row, folder):
    d = json.loads((folder / f'm12-pre-{SLUG[row]}.json').read_text())
    assert d['row'] == row and d['working_bits'] == P and d['pre_bits'] == PRE
    ctx.prec = P + 512
    X = dyadic_ball(d['root_lower'], d['root_upper'], PRE)
    return X


def stage_deriv(row, folder):
    start = time.monotonic()
    X = load_pre(row, folder)
    b = X.rel_accuracy_bits()
    goal = P - b + 160
    ctx.prec = goal + 96
    D = integrals(X, True, goal=goal)
    assert D.is_finite() and D > 0
    assert D.rel_accuracy_bits() >= goal - 64, ('derivative accuracy', D.rel_accuracy_bits(), goal)
    lo, hi = endpoints(D)
    rl, ru = endpoints(X)
    data = dict(row=row, working_bits=P, goal_bits=goal, relative_bits=D.rel_accuracy_bits(),
                root_lower=rl, root_upper=ru,
                lower=lo, upper=hi, elapsed_seconds=time.monotonic() - start,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(f'm12-deriv-{SLUG[row]}.json').write_text(json.dumps(data) + '\n')
    print('DERIVATIVE PASS', row, data['relative_bits'], 'seconds', data['elapsed_seconds'], flush=True)


def stage_shard(row, i, folder):
    start = time.monotonic()
    X = load_pre(row, folder)
    S = X.mid()
    N, _ = plan(S, P)                  # ctx.prec = P
    m = N // 4
    lo, hi = bounds(m, i, K)
    aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
    step = arb.pi() / (2 * m)
    total = arb(0)
    for j in range(lo, hi):
        total += node(S, aS, step, j)
    assert total.is_finite() and total > 0
    assert total.rel_accuracy_bits() >= P - 100
    l, u = endpoints(total)
    data = dict(row=row, working_bits=P, N=N, index=i, shards=K, lo=lo, hi=hi,
                midpoint=endpoints(S)[0], lower=l, upper=u,
                elapsed_seconds=time.monotonic() - start)
    Path(f'm12-shard-{SLUG[row]}-{i}.json').write_text(json.dumps(data) + '\n')
    print('SHARD PASS', row, i, 'nodes', hi - lo, 'of', m - 1, 'relative bits',
          total.rel_accuracy_bits(), 'seconds', data['elapsed_seconds'], flush=True)


def final_root(row, folder):
    X = load_pre(row, folder)
    b = X.rel_accuracy_bits()
    d = json.loads((folder / f'm12-deriv-{SLUG[row]}.json').read_text())
    assert d['row'] == row and d['working_bits'] == P
    assert (d['root_lower'], d['root_upper']) == endpoints(X)
    D = dyadic_ball(d['lower'], d['upper'])
    assert D > 0
    S = X.mid()
    assert S.rad() == 0
    N, tail = plan(S, P)
    m = N // 4
    aS = arb(1) / 2 + 1 / S.expm1() - 1 / S
    total = 2 * aS / S
    end = 1
    for i in range(K):
        s = json.loads((folder / f'm12-shard-{SLUG[row]}-{i}.json').read_text())
        lo, hi = bounds(m, i, K)
        assert (s['row'], s['working_bits'], s['N'], s['index'], s['shards'], s['lo'], s['hi']) == \
               (row, P, N, i, K, lo, hi)
        assert s['midpoint'] == endpoints(S)[0]
        assert lo == end and hi > lo
        end = hi
        x = dyadic_ball(s['lower'], s['upper'], P - 100)
        total += x
    assert end == m
    H = S * S * total / (2 * N) + arb(0, tail.upper())
    assert H.rel_accuracy_bits() >= P - 100 and H > 0
    ctx.prec = P
    Y = S - (H - common.exact(Q(row))) / D
    assert Y.is_finite() and Y > 0
    Z = X.intersection(Y)
    assert Z.rel_accuracy_bits() > b
    F = A(acb(Z)).real ** 2 / 4
    print('FINAL ROOT', row, 'root bits', Z.rel_accuracy_bits(), 'F bits', F.rel_accuracy_bits(), flush=True)
    assert F.rel_accuracy_bits() >= P - 120, ('F accuracy', F.rel_accuracy_bits())
    printed_check(row, F)
    return Z, F


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
        Z, F = final_root(row, folder)
        profiles[row] = (Z, F)
    ctx.prec = P
    coeffs = {}
    for M in (100, 200, 400):
        d = json.loads((root / f'm12-lanczos-{M}.json').read_text())
        assert d['M'] == M and d['working_bits'] == common.WORK
        assert set(d['values']) == {str(j) for j in (M // 4, M // 2, M, 2 * M, 4 * M)}
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
        source_runs=[44313014167, int(os.environ.get('GITHUB_RUN_ID', '0'))],
        roots=roots, checks=checks), indent=2) + '\n')
    print(f'TABLE {P} SUCCESS', len(checks), 'checks', 'minimum relative bits',
          min(x['relative_bits'] for x in checks), flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('stage', choices=['pre', 'deriv', 'shard', 'certify'])
    ap.add_argument('row', nargs='?', choices=list(SLUG))
    ap.add_argument('--index', type=int, default=0)
    ap.add_argument('--folder', type=Path, default=Path('.'))
    ns = ap.parse_args()
    if ns.stage == 'pre':
        stage_pre(ns.row)
    elif ns.stage == 'deriv':
        stage_deriv(ns.row, ns.folder)
    elif ns.stage == 'shard':
        assert 0 <= ns.index < K
        stage_shard(ns.row, ns.index, ns.folder)
    else:
        stage_certify(ns.folder)
