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

These are **deposited obligations, not certificates** unless the
corresponding SHA-specific GitHub CI has succeeded with a clean
`#print axioms` result. The Step 3 estimate, Step 4
unconditional strong convergence, Step 5 equality of operator
norms and the noise estimate are distinct formalization obligations.

**This note belongs solely to V007. No merge into V097 and no V170 changes.**
