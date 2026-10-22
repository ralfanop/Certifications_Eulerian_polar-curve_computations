#!/usr/bin/env python3
"""Produce transparent proof witnesses; Lean checks, rather than trusts, them."""
from pathlib import Path
from math import lcm,gcd
from flint import fmpq_poly as Poly, fmpq
import json
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'results/independent_exact.json').read_text())
src=json.loads((ROOT/'inputs/V033_Lanczos_beta5_beta16_exact.json').read_text())
L=int(data['moment_common_denominator'])
def poly(a): return Poly([fmpq(x) for x in a])
def ilist(p):
    return '['+', '.join(str(int(c)) for c in p)+']'
def qlist(p):
    return '['+', '.join('('+str(c.p)+':ℚ)/'+str(c.q) for c in p)+']'
mu=[poly(a)*L for a in data['moments']]
allmu=[mu[k//2] if k%2==0 else Poly([]) for k in range(33)]
lines=['import V033Core','namespace V033','set_option maxRecDepth 20000',
       'set_option maxHeartbeats 2000000',f'def momentDenominator : ℤ := {L}',
       'def scaledMoments : List (List ℤ) := ['+',\n'.join(ilist(p) for p in allmu)+']']
ws=[];cs=[];hs=[]
for n,pp in enumerate(data['monic_polynomials']):
    den=Poly([1])
    for a in pp:
        d=poly(a['d']);den=(den*d)//den.gcd(d)
    cp=[poly(a['n'])*(den//poly(a['d'])) for a in pp]
    common=lcm(*(int(c.q) for p in cp+[den] for c in p))
    den*=common;cp=[p*common for p in cp]
    g=gcd(*(int(c) for p in cp+[den] for c in p))
    den/=g;cp=[p/g for p in cp]
    assert cp[-1]==den
    h=sum((p*allmu[i+n] for i,p in enumerate(cp)),Poly([]))
    ws.append(cp);cs.append(den);hs.append(h)
    lines += [f'def coeff{n} : List (List ℤ) := ['+',\n'.join(ilist(p) for p in cp)+']',
              f'def monicDen{n} : List ℤ := {ilist(den)}',
              f'def normNum{n} : List ℤ := {ilist(h)}']
for n in range(5,17):
    b=src['beta'][str(n)]
    lines += [f'def betaNum{n} : List ℤ := {ilist(poly(b["numerator"]))}',
              f'def betaDen{n} : List ℤ := {ilist(poly(b["denominator"]))}']
lines+=['end V033']
(ROOT/'lean/V033Data.lean').write_text('\n'.join(lines)+'\n')

for n in range(17):
    lines=['import V033Data','namespace V033','set_option maxRecDepth 20000',
           'set_option maxHeartbeats 5000000']
    lines += [f'theorem monic_{n} : coeff{n}[{n}]?.getD [] = monicDen{n} := by decide']
    for k in range(n):
        lines += [f'theorem orthog_cert_{n}_{k} : pzero (momentCombination scaledMoments coeff{n} {k}) = true := by decide',
                  f'theorem orthog_{n}_{k} (M : ℝ) : realCombination scaledMoments M coeff{n} {k} = 0 :=\n  checked_orthogonality _ _ _ orthog_cert_{n}_{k} M']
    lines += [f'theorem norm_cert_{n} : pzero (psub (momentCombination scaledMoments coeff{n} {n}) normNum{n}) = true := by decide']
    if n>=5:
        lines += [f'theorem ratio_cert_{n} : pzero (psub (pmul (pmul betaNum{n} normNum{n-1}) monicDen{n})\n (pmul (pmul betaDen{n} normNum{n}) monicDen{n-1})) = true := by decide',
            f'theorem ratio_{n} (M : ℝ) (hD : peval betaDen{n} M ≠ 0) (hH : peval normNum{n-1} M ≠ 0)\n (hC : peval monicDen{n} M ≠ 0) (hCp : peval monicDen{n-1} M ≠ 0) :\n peval betaNum{n} M / peval betaDen{n} M =\n (peval normNum{n} M / peval monicDen{n} M) / (peval normNum{n-1} M / peval monicDen{n-1} M) :=\n checked_norm_ratio _ _ _ _ _ _ ratio_cert_{n} M hD hH hC hCp',
            f'#print axioms ratio_cert_{n}',f'#print axioms ratio_{n}']
    lines+=['end V033']
    (ROOT/f'lean/V033Degree{n}.lean').write_text('\n'.join(lines)+'\n')
print('Generated monic, all lower-monomial orthogonality, norm and ratio certificates.')
