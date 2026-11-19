# M14 equation (225): exact composition residual and unconditional analytic bound

Frozen version: Manuscript_14_Dominant_Pole_Preliminaries_20261117 (1).zip,
SHA256 b8285caa19e3ad809951b570f1f02abcfbfef845992681195f9283631b262171
per the existing frozen-version reconciliation. Label eq:parry-index-asymptotics.

This addresses the finite-composition obligation explicitly left open by #441/#443
(which own the concurrent actual-log Lean work), and uses the integrated
#75, #362 and #371 modules. No manuscript is edited.

## Exact finite algebra

Put t=x², B=sinh(x)/x, ε=B−1, u=6ε/t−1,
E(t)=Σ_{j=1}^{12} t^j/(2j+1)!, N(t)=6E(t)/t−1 (the latter is a polynomial),
and F_n(y)=Σ_{k=1}^n (−1)^(k+1)y^k/k.
A12, C12, P12, R12 are exactly the polynomials of
V14119ParryResidualTransferX20.lean.

The independent exact-rational script numerics/exact/m14_parry_composition_residual.py
constructs the entire compositions (not just their first coefficients).
It proves coefficient equality through degree 12 for F_12(E) vs t A12,
and degree 11 for F_11(N) vs C12. It checks the sums of the absolute values
of ALL residual coefficients (132 and 110 respectively) are <1/1000.
Therefore for every real |t|≤1,
* |F_12(E(t))−t A12(t)| ≤ |t|^13/1000;
* |F_11(N(t))−C12(t)| ≤ |t|^12/1000.

It also proves the absolute coefficient sums of E and N are <1/4 and <1/16.
These are exact integer/rational calculations, not interval overlap or
pointwise samples.

## Unconditional mathematical derivation

For 0<x≤1, t∈(0,1], the certified sinh Taylor bounds of #362 give
|ε−E(t)|≤t^13 and |u−N(t)|≤6t^12: substitute the explicit degree-25 sinh sum
and divide by x, then by x² as appropriate.
The #75 positive epsilon enclosures imply t/6≤ε≤t/4 and 0≤u≤t/16.
Consequently all four actual and proxy arguments have modulus ≤1;
the actual arguments are nonnegative and ≤1/2.

For |v|,|w|≤1 the identity v^k−w^k=(v−w)Σ_{j=0}^{k−1}v^j w^(k−1−j)
shows |v^k−w^k|≤k|v−w|. Summing termwise in F_n shows
|F_n(v)−F_n(w)|≤n|v−w|.

By the actual logarithm Taylor remainder theorem of #362,
|log B−F_12(ε)|≤2 ε^13≤2t^13 and
|log(6(B−1)/t)−F_11(u)|≤2u^12≤2t^12.
Combining Taylor, argument replacement, and exact finite residual:
|log B/t−A12(t)|≤(2+12+1/1000)t^12≤15t^12;
|log(6(B−1)/t)−C12(t)|≤(2+11·6+1/1000)t^12≤69t^12.

B>1 by ε≥t/6. The elementary bound log(1+y)≥2y/(2+y) for y≥0
(used in #75) gives log B≥2ε/(2+ε)≥ε/2≥t/12 since ε≤1/4<2.
Also log(6/t)≥log 6≥10/7>1. Thus all hypotheses of the proved
#371 parry_expansion_transfer hold with K=15 and L=69. Its conclusion is

|log(1/(B−1))/log B − (P12(t) log(6/t)+R12(t))/t|
  ≤ 3373 t^11 log(6/t).

For 0<x≤1/6, log 6≤log(1/x), so log(6/t)≤3log(1/x).
Hence the error is at most 10119 x^22 log(1/x), establishing the
unconditional big-O mathematically with explicit constants.

## Verification scope

The rational residual calculation passed locally using Python Fraction.
The analytic argument above is complete as a mathematical derivation from
the indicated proved inequalities, but the new composition/substitution
lemmas and final theorem have NOT yet been checked by the Lean kernel.
Check exact-head CI for the integer/rational audit and then formalize the
composition via coefficient residuals, the telescoping power inequality
and #371's transfer. Do not count this as a new Arb scalar certification
or an all-Lean certificate. Existing Arb evidence is unchanged. No merge.
