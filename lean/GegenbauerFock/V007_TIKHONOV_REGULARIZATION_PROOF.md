# V007 — Tikhonov regularization of the genuine Gegenbauer–Fock Gram

## Operator setting

Let `H = L²(ν_λ;ℂ)`, `K` be the full Fock coefficient Hilbert space,
`C=C_{λ,α}:H→K` the genuine compact, injective transform, and
`G=C* C:H→H` the genuine positive compact source Gram. Parameters
`λ,α>0` are fixed. Earlier Lean certificates prove the positivity,
selfadjointness and injectivity of `G`, and the density of `ran G`.

For `ε>0`, set `A_ε=G+εI`, `E_ε=ε A_ε^{-1}`,
`T_ε=G A_ε^{-1}`. These are bounded operators on the original
weighted Hilbert space.

## Step 1 — Genuine shifted invertibility

The previously certified fact `−ε∈ρ(G)` gives
`A_ε∈B(H)^×`. Both
`A_ε A_ε^{-1}=I` and `A_ε^{-1}A_ε=I` hold in the full
infinite-dimensional operator algebra. Algebraically,

`I−T_ε=E_ε=ε A_ε^{-1}`.

Unlike the unshifted `G^{-1}`, each shifted inverse is bounded.

## Step 2 — Exact singular multipliers

On every actual positive Gram eigenmode `G u_i=μ_i u_i`,
`μ_i>0`, the regularized inverse and filter act as

`A_ε^{-1}u_i=(μ_i+ε)^{-1}u_i`,

`T_εu_i=[μ_i/(μ_i+ε)]u_i`,

`E_εu_i=[ε/(μ_i+ε)]u_i`.

The scalar multiplier tends to 1 for `T_ε`, and to 0 for
`E_ε`, as `ε↓0`. The mode identities must be proved for the
actual operators, not simply postulated for diagonal surrogates.

## Step 3 — Uniform contractivity

For every `x∈H`, positive definiteness of `A_ε` in the form
`⟨Gx,x⟩≥0` gives

`ε‖x‖² ≤ Re⟨A_ε x,x⟩ ≤ ‖A_ε x‖‖x‖`.

Consequently `ε‖x‖ ≤ ‖A_εx‖` and hence

`‖E_ε‖ ≤ 1`.

The estimate is uniform in all `ε>0`. This coercivity/contractivity
estimate is an *independent Lean obligation*, beyond mere invertibility.

## Step 4 — Strong convergence from the dense range

For `y∈H`,

`E_ε Gy = εy − ε E_ε y`,

so `‖E_ε Gy‖ ≤ 2ε‖y‖ → 0`.

Since `ran G` is dense in `H` and `‖E_ε‖≤1`, for every
`f∈H` and every `y∈H`,

`‖E_ε f‖ ≤ ‖f−Gy‖ + 2ε‖y‖`.

Choose `y` so that `‖f−Gy‖` is arbitrarily small, then
let `ε↓0`. It follows that `E_ε f→0`, and thus

`T_ε f → f` **strongly** for every `f∈H`.

## Step 5 — Sharp obstruction to operator-norm convergence

Zero lies in the continuous spectrum of compact injective `G`
and is not an eigenvalue. Its already-certified normalized
approximate-null vectors imply `‖E_ε‖≥1` for every
`ε>0`; together with Step 3:

`‖I−T_ε‖=‖E_ε‖=1`.

Hence there is no convergence in operator norm, despite strong
convergence on every fixed source. This is fully compatible with the
earlier kernel-checked V007 sharp uniform-error obstruction.

## Data-space Tikhonov reconstruction

For observations `g=Cf+η`, the standard estimator is
`f_ε=(G+εI)^{-1}C* g`. Its noiseless bias is
`(I−T_ε)f=E_ε f`. For noisy data, the normal-equation
factor has spectral singular coefficients `σ_i/(σ_i²+ε)`;
in particular their supremum is bounded by `1/(2√ε)`.
Thus the customary deterministic estimate is

`‖f_ε−f‖ ≤ ‖E_εf‖ + ‖η‖/(2√ε)`.

Its full formalization in Lean requires the singular-value spectral
mapping and an operator norm estimate for the Fock-to-source
reconstruction map, which is *not* inferred from positive-shift
invertibility alone.

## Certification boundary

New Lean sources on the PR #16 Draft branch:

- `CanonicalCFCGramTikhonovShift.lean`:
  positivity-shift unit and two-sided operator inverse;
- `CanonicalCFCGramTikhonovEigenmodes.lean`:
  exact actual Gram eigenmode multiplier;
- `CanonicalCFCGramTikhonovErrorIdentity.lean`:
  the global identity `I−T_ε=E_ε`.

The first three operator-level components listed above are **now certified** by
[CI #41498115168](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41498115168),
SUCCESS on source commit `075c9e8106d9d9eda7feff42819a390f768c1943`.
The exact positive-shift unit, both inverse identities, actual positive Gram eigenmode
filters and the full-space bounded-operator error identity
`I - T_eps = E_eps` passed the pinned Lean compiler and explicit `#print axioms`
audit with only `propext`, `Classical.choice`, `Quot.sound` and no
`sorryAx` or `Lean.ofReduceBool`. The source blobs of the three Lean modules
are unchanged on the V007 Draft branch as of 3 November 2026.

**Step 3 and dense-range error: KERNEL-CERTIFIED on 4 November 2026.**
[CI #41804268333](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804268333)
is **SUCCESS** at source commit
[`4144a28d`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/4144a28d8a29b2ac301c320d49fa79c18eeaa641).
The job compiled **9,127 Lean/Lake targets** and explicitly audited five theorems.
Their `#print axioms` output listed only `propext`, `Classical.choice`,
and `Quot.sound`, without `sorryAx` or `Lean.ofReduceBool`:

- `sourceGram_positive_shift_norm_lower` — exact Gram coercivity
  `eps * ‖x‖ ≤ ‖(G+eps I)x‖`;
- `sourceGramTikhonov_error_pointwise_contract` —
  `‖eps (G+eps I)⁻¹ x‖ ≤ ‖x‖`;
- `sourceGramTikhonov_error_opNorm_le_one` —
  `‖eps (G+eps I)⁻¹‖ ≤ 1`;
- `sourceGramTikhonov_error_on_range` —
  exact identity `E_eps(Gy) = eps(y-E_eps(y))`;
- `sourceGramTikhonov_error_on_range_norm` —
  quantitative bound `‖E_eps(Gy)‖ ≤ 2eps‖y‖`.

This certification resolves earlier FAILED CI attempts
[#41717581132](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41717581132)
and [#41722695849](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41722695849),
which failed on proof-tactic elaboration (not on an analytic counterexample).

**Step 4: full-`L²` strong convergence under final dedicated CI review.**
The new source
`CanonicalCFCGramTikhonovStrongConvergence.lean` supplies the
quantitative approximation
`‖E_eps f‖ ≤ ‖f-Gy‖+2eps‖y‖`, the bridge from the actual
`gram_dense_range` theorem to `DenseRange G`, and the two desired
`Tendsto` declarations.
The first two were compiled with standard-axiom audits in failed CI
[#41804268427](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804268427);
the last two required a neighborhood-filter elaboration correction
and an explicit argument to `dist_zero_right`. Commit
[`6331f183`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/6331f183014a76dc14a913105147da64980bea97)
submitted those corrections to CI
[#41805350981](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805350981).
**Do not treat Step 4 as kernel-certified until this exact-SHA CI
reports SUCCESS and its four axiom audits have been checked.**

**Step 5 (sharp operator-norm obstruction)** and the data-space noise
estimate require independent Lean declarations and CI checks. No result about the
unshifted bounded inverse of compact `G` is asserted.

**This note belongs solely to V007. No merge into V097 and no V170 changes.**
