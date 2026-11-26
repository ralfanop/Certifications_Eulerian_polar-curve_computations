#!/usr/bin/env python3
"""Targeted refinement of M12 Table 1 from the certified step-2 root balls.
Only the residual H at one exact midpoint per row is recomputed, using the
same certified periodic-strip tail and complete shard coverage as #495.
The fixed derivative enclosure on W from #490 is reused by the mean value
theorem; both the previous root enclosure and the evaluation point must lie
in W. No new unvalidated approximation is treated as an enclosure.
"""
import argparse
import json
import math
import os
from pathlib import Path
from fractions import Fraction as Q

import million_decimal_common as common
import m12_table_1000000 as newton
from m12_table_68000 import dyadic_ball, rounded, SLUG, PROFILES, ROWS
from m12_profile_interval_newton import A, printed_check
from flint import arb, acb, ctx, fmpz

DIGITS = 70000
OLD = 68000
RESIDUAL_BITS = 240000
PREC = 250000
NEED = math.ceil(DIGITS * math.log2(10)) + 64
ROOT_BITS = 235000
assert newton.P == 1000000 and not newton.SMOKE


def old_root(row, folder):
    d = json.loads((folder / f'm12m-x2-{SLUG[row]}.json').read_text())
    assert (d['row'], d['working_bits'], d['step']) == (row, 1000000, 2)
    ctx.prec = newton.P + 512
    return newton.dyadic_ball(d['root_lower'], d['root_upper'], 226900)


def midpoint(k, row, folder):
    assert k == 3
    Z = old_root(row, folder)
    ctx.prec = RESIDUAL_BITS - 64
    S = (Z.mid() * 1).mid()
    assert S.rad() == 0 and S > 0
    return S, RESIDUAL_BITS, Z.rel_accuracy_bits(), 0


# Reuse the certified quadrature and shard-combiner, but not the million-bit
# next-point heuristic: the old enclosure's midpoint suffices for this target.
newton.point = midpoint


def refine(row, folder):
    W, D, _ = newton.ball_and_derivative(row, folder)
    Z = old_root(row, folder)
    assert W.contains(Z) and D > 0
    S, H, p, _, _ = newton.residual(3, row, folder)
    assert p == RESIDUAL_BITS and W.contains(S)
    ctx.prec = p + 64
    Y = S - (H - newton.target(row)) / D
    assert Y.is_finite() and Y.overlaps(Z)
    X = Z.intersection(Y)
    assert X > 0 and X.rel_accuracy_bits() >= ROOT_BITS
    lo, hi = newton.endpoints(X)
    result = dict(row=row, root_lower=lo, root_upper=hi,
                  relative_bits=X.rel_accuracy_bits(), residual_bits=p,
                  prior_relative_bits=Z.rel_accuracy_bits(),
                  derivative_relative_bits=D.rel_accuracy_bits())
    (folder / f'm12-70000-root-{SLUG[row]}.json').write_text(json.dumps(result) + '\n')
    print('ROOT 70000 PASS', row, Z.rel_accuracy_bits(), '->',
          X.rel_accuracy_bits(), 'derivative', D.rel_accuracy_bits(), flush=True)


def fixed_integer(x, digits):
    scale = fmpz(10) ** digits
    lo, hi = x.lower().fmpq(), x.upper().fmpq()
    a, b = 2 * lo.p * scale, 2 * hi.p * scale
    m = (a + lo.q) // (2 * lo.q)
    assert a > (2 * m - 1) * lo.q and b < (2 * m + 1) * hi.q
    return str(m)


def certify(folder):
    ctx.prec = PREC
    old = json.loads((folder / 'm12-table-68000.json').read_text())
    assert old['significant_digits'] == OLD and old['fixed_decimal_places'] == OLD
    assert len(old['checks']) == 25
    previous = {d['name']: d for d in old['checks']}
    profiles, roots = {}, {}
    for row, slug in SLUG.items():
        d = json.loads((folder / f'm12-70000-root-{slug}.json').read_text())
        assert d['row'] == row and d['residual_bits'] == RESIDUAL_BITS
        Z = dyadic_ball(d['root_lower'], d['root_upper'])
        assert Z.rel_accuracy_bits() >= ROOT_BITS
        o = old['roots'][row]
        assert Z.overlaps(dyadic_ball(o['root_lower'], o['root_upper']))
        F = A(acb(Z)).real ** 2 / 4
        printed_check(row, F)
        roots[row] = d
        profiles[row] = F
    coeffs = {}
    for M in (100, 200, 400):
        d = json.loads((Path('sources') / f'm12-lanczos-{M}.json').read_text())
        assert d['M'] == M and d['working_bits'] == common.WORK
        assert set(d['values']) == {str(j) for j in (M//4, M//2, M, 2*M, 4*M)}
        coeffs[M] = {j: dyadic_ball(v['lower'], v['upper']) for j,v in d['values'].items()}
    checks = []

    def check(name, x, printed, unit):
        assert x.is_finite() and x > 0 and x.rel_accuracy_bits() >= NEED, (name, x.rel_accuracy_bits(), NEED)
        d = Q(printed)
        assert common.exact(d-unit/2) < x < common.exact(d+unit/2)
        o = previous[name]
        assert o['printed'] == printed and x.overlaps(dyadic_ball(o['lower'], o['upper']))
        assert rounded(x, OLD) == o['rounded_significant']
        assert fixed_integer(x, OLD) == o['rounded_scaled_integer']
        sig = rounded(x, DIGITS)
        fixed = fixed_integer(x, DIGITS)
        checks.append(dict(name=name, printed=printed, relative_bits=x.rel_accuracy_bits(),
                           rounded_significant=sig, rounded_scaled_integer=fixed,
                           lower=str(x.lower().fmpq()), upper=str(x.upper().fmpq())))
        print('TABLE 70000 PASS', name, x.rel_accuracy_bits(), flush=True)

    for t,*ds in ROWS:
        F = profiles[t]
        check('F('+t+')', F, PROFILES[t], Q(1,10**7))
        for M, displayed in zip((100,200,400), ds[:3]):
            j = Q(t)*M
            assert j.denominator == 1
            E = coeffs[M][str(j.numerator)]-F
            check('M*E t='+t+' M='+str(M), M*E, displayed, Q(1,10**6))
            if M == 400:
                check('E t='+t+' M=400', E, ds[3], Q(1,10**7))
    assert len(checks)==25 and {x['name'] for x in checks}==set(previous)
    Path('m12-table-70000.json').write_text(json.dumps(dict(
        significant_digits=DIGITS, fixed_decimal_places=DIGITS,
        working_precision=PREC, residual_bits=RESIDUAL_BITS,
        source_runs=[44313014167,44782807031,44898333059,45043079648,
                     int(os.environ.get('GITHUB_RUN_ID','0'))],
        roots=roots, checks=checks), indent=2)+'\n')
    print('TABLE 70000 SUCCESS 25 checks minimum relative bits',
          min(x['relative_bits'] for x in checks), 'needed', NEED, flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['matrix','worker','combine'])
    ap.add_argument('--row', choices=SLUG)
    ap.add_argument('--index', type=int)
    ap.add_argument('--folder', type=Path, default=Path('inputs'))
    ns = ap.parse_args()
    if ns.mode == 'matrix':
        print(json.dumps(newton.matrix(json.dumps([['r3',r] for r in SLUG]),ns.folder)))
    elif ns.mode == 'worker':
        assert ns.row is not None and ns.index is not None
        newton.stage_r(3,ns.row,ns.index,ns.folder)
    else:
        for row in SLUG:
            refine(row,ns.folder)
        certify(ns.folder)
