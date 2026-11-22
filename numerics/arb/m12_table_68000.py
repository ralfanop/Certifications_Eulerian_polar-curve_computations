#!/usr/bin/env python3
"""M12 Table 1: strict rounding of the 25 printed cells to 68000 significant
digits and to 68000 fixed decimal places.

Inputs, each authenticated by run, artifact id and SHA-256 digest
(.github/workflows/m12-table-68000.yml):
  * the roots of step 2 of the staged 1000000-bit pipeline
    (m12m-x2-<row>.json in the artifact m12m-bundle-step2 of run 44898333059,
    head 8962f731 of the branch m12-table-1000000-20261120).  Each is an
    interval Newton enclosure, intersected with the enclosures of steps 0 and 1,
    computed by numerics/arb/m12_table_1000000.py (stage x2) from the certified
    100000-bit roots and derivative enclosures of run 44782807031; it has at
    least 226971 relative bits;
  * the Lanczos endpoints m12-lanczos-<M>.json of run 44313014167, M = 100,
    200, 400 (about 3400000 bits);
  * m12-table-100000.json of run 44782807031 (29000 digits), used only as a
    cross-check: every new enclosure must overlap the old one, and its strict
    rounding to 29000 significant digits must equal the old one.

No root is recomputed.  For each row, F(t) = (Re A(Z))^2/4 is evaluated in Arb
on the root ball Z, and the 25 cells (F(t); M E for M = 100, 200, 400; E for
M = 400, with E = beta - F) are checked against the printed values of Table 1
and rounded strictly: both endpoints of each enclosure round to the same
68000 significant digits and to the same 68000 fixed decimal places.

Usage: m12_table_68000.py --folder DIR   (DIR holds the x2 files,
m12-table-100000.json and sources/m12-lanczos-<M>.json)
"""
import argparse
import json
import math
import os
from fractions import Fraction as Q
from pathlib import Path

import million_decimal_common as common   # python-flint 0.9.0, no int-str limit
from flint import arb, acb, fmpq, fmpz, ctx
from m12_profile_interval_newton import A, printed_check
from m12_profile_interval_newton import ROWS as PROFILES
from m12_table_final_errors import ROWS

DIGITS = 68000
OLD_DIGITS = 29000
PREC = 240000                       # working precision, above the root accuracy
ROOT_BITS = 226900                  # every root ball has at least this accuracy
NEED = math.ceil(DIGITS * math.log2(10)) + 64
SLUG = {'1/4': 'quarter', '1/2': 'half', '1': 'one', '2': 'two', '4': 'four'}


def dyadic_ball(l, u):
    lo, hi = fmpq(l), fmpq(u)
    assert 0 < lo <= hi
    for q in (lo, hi):
        assert q.q > 0 and (q.q & (q.q - 1)) == 0
    x = arb(lo).union(arb(hi))
    assert x.lower().fmpq() <= lo and hi <= x.upper().fmpq()
    return x


def endpoints(x):
    return str(x.lower().fmpq()), str(x.upper().fmpq())


def rounded(x, digits):
    common.DIGITS = digits
    return common.rounded_significant(x)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--folder', type=Path, required=True)
    folder = ap.parse_args().folder
    ctx.prec = PREC
    old = json.loads((folder / 'm12-table-100000.json').read_text())
    assert old['working_bits'] == 100000 and old['significant_digits'] == OLD_DIGITS
    assert len(old['checks']) == 25
    old_checks = {c['name']: c for c in old['checks']}

    profiles, roots = {}, {}
    for row, slug in SLUG.items():
        d = json.loads((folder / f'm12m-x2-{slug}.json').read_text())
        assert d['row'] == row and d['working_bits'] == 1000000 and d['step'] == 2
        Z = dyadic_ball(d['root_lower'], d['root_upper'])
        assert Z.rel_accuracy_bits() >= ROOT_BITS, (row, Z.rel_accuracy_bits())
        assert d['relative_bits'] >= ROOT_BITS
        X = dyadic_ball(old['roots'][row]['root_lower'], old['roots'][row]['root_upper'])
        assert X.overlaps(Z), ('root', row)
        F = A(acb(Z)).real ** 2 / 4
        printed_check(row, F)
        profiles[row] = F
        roots[row] = dict(root_lower=d['root_lower'], root_upper=d['root_upper'],
                          relative_bits=Z.rel_accuracy_bits())
        print('ROOT', row, 'relative bits', Z.rel_accuracy_bits(), flush=True)

    coeffs = {}
    for M in (100, 200, 400):
        d = json.loads((folder / 'sources' / f'm12-lanczos-{M}.json').read_text())
        assert d['M'] == M and d['working_bits'] == common.WORK
        assert set(d['values']) == {str(j) for j in (M // 4, M // 2, M, 2 * M, 4 * M)}
        coeffs[M] = {j: dyadic_ball(v['lower'], v['upper']) for j, v in d['values'].items()}

    scale = fmpz(10) ** DIGITS
    checks = []

    def check(name, x, printed, unit):
        assert x.is_finite() and x > 0
        assert x.rel_accuracy_bits() >= NEED, (name, x.rel_accuracy_bits(), NEED)
        d = Q(printed)
        assert common.exact(d - unit / 2) < x < common.exact(d + unit / 2), name
        significant = rounded(x, DIGITS)
        lo, hi = x.lower().fmpq(), x.upper().fmpq()
        a, b = 2 * lo.p * scale, 2 * hi.p * scale
        m = (a + lo.q) // (2 * lo.q)
        assert a > (2 * m - 1) * lo.q and b < (2 * m + 1) * hi.q, name
        o = old_checks[name]
        assert o['printed'] == printed, name
        assert x.overlaps(dyadic_ball(o['lower'], o['upper'])), ('old enclosure', name)
        assert rounded(x, OLD_DIGITS) == o['rounded_significant'], ('old digits', name)
        checks.append(dict(name=name, printed=printed, relative_bits=x.rel_accuracy_bits(),
                           rounded_significant=significant, rounded_scaled_integer=str(m),
                           lower=str(lo), upper=str(hi)))
        print('TABLE 68000 PASS', name, x.rel_accuracy_bits(), flush=True)

    for t, *ds in ROWS:
        F = profiles[t]
        check('F(' + t + ')', F, PROFILES[t], Q(1, 10 ** 7))
        for M, displayed in zip((100, 200, 400), ds[:3]):
            j = Q(t) * M
            assert j.denominator == 1
            E = coeffs[M][str(j.numerator)] - F
            check('M*E t=' + t + ' M=' + str(M), M * E, displayed, Q(1, 10 ** 6))
            if M == 400:
                check('E t=' + t + ' M=400', E, ds[3], Q(1, 10 ** 7))
    assert len(checks) == 25
    Path('m12-table-68000.json').write_text(json.dumps(dict(
        significant_digits=DIGITS, fixed_decimal_places=DIGITS, working_precision=PREC,
        source_runs=[44313014167, 44782807031, 44844906618, 44867669410, 44898333059,
                     int(os.environ.get('GITHUB_RUN_ID', '0'))],
        roots=roots, checks=checks), indent=2) + '\n')
    print('TABLE 68000 SUCCESS', len(checks), 'checks', 'minimum relative bits',
          min(c['relative_bits'] for c in checks), 'needed', NEED, flush=True)


if __name__ == '__main__':
    main()
