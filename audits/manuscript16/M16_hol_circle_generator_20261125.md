# M16 §14.5 `eq:hol-integral`: the self-adjoint operator `B = (D − φ)² + a²` on `L²(S¹)` with domain `H²(S¹)` — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyCircleGenerator20261125.lean` (29 audited declarations), SHA-256
`31c54150cb9cd12af255b4aa1aa6b33f938f6283b096ee81417040740f33bcad`. It imports `Mathlib`,
`Manuscript16.HolonomyCircleResolvent20261125` (#599, merged as `b9ee66b2`) and
`Manuscript16.RobinDirichletRealisation20261125` (#611, merged through `be053cf5`), both unchanged in
`main` = `259f8b1df8a124f1c05cf92ccc71aeeb3eaa557f` (branch base) and not re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` (row `eq:hol-integral`, operator
realisation on `L²(S¹)`, #599) lists as not claimed: "unbounded self-adjoint `B` on `H²(S¹)` and
`resolvent = B⁻¹` as its inverse, basis-independent trace (trace class)". This file discharges the
first two items. No open PR touches Manuscript 16 or 17 (checked 25 Nov 2026, 21:00 UTC through the
REST API: the open PRs #616, #615, #614, #584, #582, #581, #565, #563, #394 concern M11–M14 and #474
concerns `SharedCore` trace files; none touches `lean/Manuscript16`, `lean/Manuscript17` or the M16/M17
audits).

## Statements

`S¹ = ℝ/2πℤ` with normalised Haar measure, `L2Circle = L²(S¹)`, `e_n(θ) = e^{inθ}` (Mathlib
`fourierBasis`), `b_n = circleEig a φ n = (n − φ)² + a²`, `a > 0`, `φ` real, `D = −i d/dθ`;
`resolvent a φ` is the bounded Fourier multiplier with symbol `1/b_n` of #599.

| Declaration | Statement |
|---|---|
| `generator a φ` | `B = resolvent⁻¹` as a Mathlib `LinearPMap` on `L²(S¹)`: graph `{(resolvent f, f)}`, domain `ran resolvent` (the merged `realisation K t` of #611 with `t = 0`) |
| `generator_isSelfAdjoint` | **`B` is self-adjoint** (`IsSelfAdjoint`: equal to its `LinearPMap.adjoint`, dense domain) |
| `H2Circle` | `H²(S¹)` in Fourier form: `{u ∈ L²(S¹) : ∑_{n∈ℤ} (1 + n²)² |⟪e_n, u⟫|² < ∞}` |
| `generator_domain_eq` | **`dom B = H²(S¹)`** |
| `mem_range_resolvent_iff`, `summable_circleEig_iff` | `u ∈ ran resolvent ⇔ ∑ b_n² |û_n|² < ∞ ⇔ ∑ (1 + n²)² |û_n|² < ∞` (`circleEig_le`, `one_add_sq_le`: `b_n ≤ (2 + 2φ² + a²)(1 + n²)`, `1 + n² ≤ ((2a² + 1 + 2φ²)/a²) b_n`) |
| `generator_resolvent`, `resolvent_generator` | **`B (resolvent f) = f` for every `f ∈ L²(S¹)`, `resolvent (B u) = u` for every `u ∈ dom B`**: `resolvent = B⁻¹` |
| `repr_generator`, `inner_mode_generator` | `⟪e_n, B u⟫ = b_n ⟪e_n, u⟫` for every `u ∈ dom B` |
| `circleMode_mem_domain`, `generator_mode` | `e_n ∈ dom B`, `B e_n = b_n e_n` |
| `generator_eigenvalue_iff` | `μ` is an eigenvalue of `B` iff `μ = b_n` for some `n ∈ ℤ` |
| `liftC`, `liftC_coe`, `liftL2` | for continuous `u : ℝ → ℂ` of period `2π`: the induced continuous function on `S¹`, with value `u θ` at the class of `θ`, and its class in `L²(S¹)` |
| `repr_liftL2`, `fourierCoeffOn_deriv` | `⟪e_n, [u]⟫` is the Fourier coefficient of `u` on `[0, 2π]`; `(u′)^_n = i n û_n` for `u ∈ C¹` of period `2π` |
| `repr_liftL2_twistedOp` | for `u ∈ C²` of period `2π`: the Fourier coefficients of `−u″ + 2iφu′ + (φ² + a²)u` are `b_n û_n` |
| `generator_twistedOp` | **for every `C²` function `u` of period `2π`, `[u] ∈ dom B` and `B [u] = [−u″ + 2iφu′ + (φ² + a²)u]`**: `B` acts as the differential expression `(D − φ)² + a²` on all of `C²(S¹)`, not only on the modes |
| `hol_integral_generator` | manuscript form: all of the above together |

The remaining declarations are glue (`repr_eq_inner`, `ext_repr`, `repr_resolvent`,
`mem_generator_domain`, `resolvent_mem_domain`, `zero_lt_two_pi'`, `periodic_deriv`,
`contDiff_two_aux`, `twistedOp_continuous`, `twistedOp_periodic`).

## Method

`B` is the merged abstract `t + K⁻¹` of #611 with `K = resolvent` (bounded, self-adjoint, injective
by #599) and `t = 0`, so its self-adjointness is not re-proved. The domain is identified through the
Fourier coefficients: `ran resolvent` consists of the `u` with `(b_n û_n) ∈ ℓ²(ℤ)` (Bessel/Parseval in
Mathlib's `fourierBasis`), and `b_n` is comparable with `1 + n²` with the explicit constants above.
On `C²` functions, the Fourier coefficients of derivatives come from Mathlib
`fourierCoeffOn_of_hasDerivAt` (integration by parts on `[0, 2π]`, boundary terms cancelled by
periodicity) and the fundamental theorem of calculus for `n = 0`; an element of `L²(S¹)` is
determined by its Fourier coefficients.

## Published results cited, not re-proved

- Fourier Hilbert basis of `L²(S¹)` and integration by parts for Fourier coefficients: Mathlib
  (`fourierBasis`, `fourierBasis_repr`, `fourierCoeff_toLp`, `fourierCoeff_liftIco_eq`,
  `fourierCoeffOn_of_hasDerivAt`).

## Not claimed

- `H2Circle` is the Fourier-coefficient definition of `H²(S¹)`. Its equivalence with the definition
  by weak derivatives in `L²(S¹)` is the classical characterisation of Sobolev spaces on the circle
  and is not formalised; what is proved about derivatives is `generator_twistedOp` on `C²(S¹)`.
- Trace-class membership of `resolvent` and basis independence of `∑_n ⟪e_n, resolvent e_n⟫`
  (Lidskii; Simon 2005): not formalised (no Schatten classes in Mathlib at the pinned commit).
- The functional calculus `e^{−2t√B}` of the unbounded `B`: the operators `evanescent a φ t` of #599
  remain Fourier multipliers; their identification with `e^{−2t√B}` through a spectral theorem for
  unbounded operators is not claimed.
- Any statement about the holonomy of a specific Maxwell field, and any geometric statement.
- The correspondence of the symbols with the printed display `eq:hol-integral` of `16.tex` was not
  re-read in the source, which is not in the repository.

## Verification

- Local, pinned toolchain (Mathlib at `0272bbe1`, cache from `lake exe cache get`): the 21 imported
  repository modules (`SharedCore/FredholmCompactParametrix`, `SharedCore/FredholmAtkinson`,
  `V165TypedGraphSchur`, `V165GraphNeumann`, `V166CompactTransfer`,
  `DiracMaxwellObstructionIndex20261124`, `DiracMaxwellGraphSpace20261124`, `V166L2SpectralInverse`,
  `V166SpectralCutoffs`, `DiracMaxwellCoefficientModel20261124`, `V166HolonomyPair`,
  `ReactiveHolonomyV166`, `HolonomyEulerProduct20261124`, `HolonomyMomentSeries20261124`,
  `HolonomyCircleResolvent20261125`, `RobinDirichletRankOne20261125`, `RobinDirichletL2Bounded20261125`,
  `RobinDirichletPositive20261125`, `RobinDirichletInjective20261125`,
  `RobinDirichletWeakResolvent20261125`, `RobinDirichletRealisation20261125`) and the new module compile
  with exit 0; the new module produces no error, warning or `Try this`; its 29 declarations depend only
  on `propext`, `Classical.choice`, `Quot.sound` (wrapped axiom lists parsed over several lines); the
  402 axiom reports of the imported modules contain only these three. The audit step of the new
  workflow was replayed locally on these logs: `SUCCESS: 29 declarations and 402 imported reports;
  standard axioms only`.
- Certifying run: `.github/workflows/m16-hol-circle-generator-20261125.yml` (exact-HEAD checkout and SHA
  assertion, pinned toolchain and Mathlib asserted, compilation of the 21 imported modules and of the new
  module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or non-standard
  axiom, artifact with per-declaration axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
