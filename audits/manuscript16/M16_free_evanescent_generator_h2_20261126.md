# M16 v16.5 §14.1, Theorem 14.1: the self-adjoint operator `−d²/dz² + α²` on `L²(ℝ)` with domain `H²(ℝ)` and inverse `R_κ(k²)` — 26 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/FreeEvanescentGenerator20261126.lean` (34 audited declarations), SHA-256
`58a89f0034c11a3b7a566353594f5c7e89abe333ed0f6ff3489bd36bc30e22eb`. It imports `Mathlib`,
`Manuscript16.FreeEvanescentResolvent20261125` (#602, merged as `5cded9bd`) and
`Manuscript16.RobinDirichletRealisation20261125` (#611, merged as `be053cf5`), both unchanged in
`main` = `780fe90f` (branch base) and not re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` (row "M16 v16.5 Theorem 14.1 (§14.1), free
evanescent resolvent on `L²(ℝ)`", #602) lists as not claimed: "domain `H²(ℝ)` and inverse identity
beyond the Schwartz core (Mathlib `TemperedDistribution.MemSobolev` exists at the pinned commit; next
step), Green kernel, Maxwell boundary realisation"; the section "Post-merge consistency of `main`
(#596 … #611)" repeats it under "Still open for Theorem 14.1". This file discharges the first item.
No open PR touches Manuscript 16 or 17 (checked 26 Nov 2026, 10:53 UTC through the REST API: the open
PRs #628, #627, #626, #616, #584, #582, #565, #563, #394 concern M11–M15 and #474 concerns
`SharedCore`/`SpecialImaginaryPoint` trace files; none touches `lean/Manuscript16`,
`lean/Manuscript17`, `lean/EulerianCert` Fefferman/Cassini files, `numerics/arb/m16*`, `m17*` or the
M16/M17 audits).

## Statements

`L2 = L²(ℝ; ℂ)` (Lebesgue measure), `fourierL2` Mathlib's unitary Fourier transform on `L²(ℝ)`
(`𝓕 f(ξ) = ∫ e^{−2πixξ} f(x) dx`), `symbol b ξ = 4π²ξ² + b`, `b > 0`; `resolvent hb` is the bounded
multiplier `𝓕⁻¹ (4π²ξ² + b)⁻¹ 𝓕` of #602. Distributions: `𝓢'(ℝ, ℂ)` of Mathlib, with its Fourier
transform and its line derivative `∂₁`.

| Declaration | Statement |
|---|---|
| `toDist`, `toDist_apply`, `toDist_injective` | the embedding `L²(ℝ) → 𝓢'(ℝ)`, `u ↦ (φ ↦ ∫ φ u)` (Mathlib `Lp.toTemperedDistributionCLM`), injective |
| `fourier_toDist`, `fourierInv_toDist` | `𝓕` and `𝓕⁻¹` on `𝓢'` restrict to Plancherel's `fourierL2`, `fourierL2.symm` |
| `smulLeftCLM_toDist` | if `G = p F` a.e. (`F, G ∈ L²`, `p` of temperate growth), then `p · F = G` in `𝓢'(ℝ)` |
| `distOp b` | `T ↦ −T'' + b T` on `𝓢'(ℝ)`, `T'' = ∂₁ ∂₁ T`, a continuous linear map |
| `fourier_distOp` | **`𝓕 (−T'' + b T) = (4π²ξ² + b) 𝓕 T`** for every `T ∈ 𝓢'(ℝ)` |
| `eq_zero_of_distOp_eq_zero` | `w ∈ L²(ℝ)`, `−w'' + b w = 0` in `𝓢'(ℝ)`, `b > 0` ⇒ `w = 0` |
| `distOp_resolvent` | **`−(R f)'' + b R f = f` in `𝓢'(ℝ)` for every `f ∈ L²(ℝ)`** |
| `resolvent_eq_iff_distOp` | `R f = u ⇔ −u'' + b u = f` in `𝓢'(ℝ)` (`f, u ∈ L²`) |
| `generator hb` | `B = R⁻¹` as a Mathlib `LinearPMap` on `L²(ℝ)`: graph `{(R f, f)}`, domain `ran R` (the merged `realisation K t` of #611 with `t = 0`) |
| `generator_isSelfAdjoint` | **`B` is self-adjoint** (`IsSelfAdjoint`: equal to its `LinearPMap.adjoint`, dense domain) |
| `generator_resolvent`, `resolvent_generator` | **`B (R f) = f` for every `f ∈ L²(ℝ)`, `R (B u) = u` for every `u ∈ dom B`**: `R = B⁻¹` |
| `toDist_generator` | **`B u = −u'' + b u` in `𝓢'(ℝ)` for every `u ∈ dom B`** |
| `mem_domain_iff_distOp`, `mem_domain_iff_secondDeriv` | `dom B = {u ∈ L² : −u'' + b u ∈ L²} = {u ∈ L² : u'' ∈ L²}` (derivatives in `𝓢'(ℝ)`): `B` is the maximal operator |
| `H2Line` | Mathlib's Sobolev space `H²(ℝ)` inside `L²(ℝ)`: `{u : MemSobolev 2 2 u}`, i.e. `𝓕⁻¹ (1 + |ξ|²) 𝓕 u ∈ L²` (Bessel potential definition) |
| `besselWeight_two`, `smulLeftCLM_symbolC`, `exists_distOp_iff_mem_H2Line` | `(1 + |ξ|²)^{2/2} = 1 + ξ²`; `(4π²ξ² + b) S = 4π² (1 + ξ²) S + (b − 4π²) S`; `−u'' + b u ∈ L² ⇔ u ∈ H²(ℝ)` |
| `generator_domain_eq` | **`dom B = H²(ℝ)`** (Mathlib's Sobolev space) |
| `generator_schwartz` | every Schwartz `u` lies in `dom B` and `B u = −u'' + b u` pointwise (`evanescentOp` of #602) |
| `re_inner_resolvent_sub_nonneg`, `re_inner_generator_ge` | `Re ⟪R f, f − b R f⟫ ≥ 0`; **`Re ⟪u, B u⟫ ≥ b ‖u‖²` for every `u ∈ dom B`** |
| `generator_sub_generator` | for `b₁, b₂ > 0`: `dom B_{b₁} = dom B_{b₂}` and `B_{b₁} u = B_{b₂} u + (b₁ − b₂) u` |
| `thm14_1_selfadjoint_realisation` | manuscript form, `α² = |κ|² − k² > 0`, `B = B_{α²}`: self-adjoint; `dom B = H²(ℝ)`; `R_κ(k²) = B⁻¹` on both sides; `B u = −u'' + α² u` in `𝓢'(ℝ)` on all of `dom B`; `Re ⟪u, B u⟫ ≥ α² ‖u‖²`; for `0 < k, k' < |κ|`, `B_{α²} u + k² u = B_{α'²} u + k'² u` on the common domain, so `H_κ = B + k²` does not depend on `k` and `(H_κ − k²)⁻¹ = R_κ(k²)` |

`distOp_apply`, `symbolC`, `symbolC_hasTemperateGrowth`, `fourierL2_resolvent_ae`,
`mem_generator_domain`, `resolvent_mem_domain` are glue.

## Method

`B` is the merged abstract `t + K⁻¹` of #611 with `K = R` (bounded, self-adjoint, injective by
#602) and `t = 0`, so its self-adjointness is not re-proved. The identification of `B` with the
differential operator is done in `𝓢'(ℝ)`: Mathlib's `fourier_lineDerivOp_eq` gives
`𝓕(−T'' + bT) = (4π²ξ² + b) 𝓕T`; since `𝓕(R f) = (4π²ξ² + b)⁻¹ 𝓕 f` almost everywhere (#602), the
pairing with Schwartz functions gives `−(R f)'' + b R f = f`. Uniqueness in `L²` uses the weight
`(1 + ξ²)⁻¹` (temperate growth, Mathlib `hasTemperateGrowth_one_add_norm_sq_rpow`), the bounded positive
function `(4π²ξ² + b)/(1 + ξ²)` and the injectivity of `L² → 𝓢'` (Mathlib
`Lp.ker_toTemperedDistributionCLM_eq_bot`). The Sobolev step uses Mathlib's
`memSobolev_iff_exists_smulLeftCLM_fourier` and the linear identity
`4π²ξ² + b = 4π²(1 + ξ²) + (b − 4π²)`; no inverse multiplier is needed.

## Published results cited, not re-proved

- Plancherel on `L²(ℝ)`, Fourier transform and line derivative on `𝓢'(ℝ)`, the Bessel-potential
  Sobolev spaces `MemSobolev`, the injectivity of `L² → 𝓢'`: Mathlib at the pinned commit.

## Not claimed

- The Green kernel `e^{−α|z−z'|}/(2α)` of `R_κ(k²)`.
- Equivalence of Mathlib's Bessel-potential `H²(ℝ)` with the definition by weak derivatives of all
  orders up to two; what is proved is `H²(ℝ) = {u ∈ L² : u'' ∈ L²}` with `u''` in `𝓢'(ℝ)`.
- The spectrum of `B` beyond the lower bound `B ≥ α²` (e.g. `σ(B) = [α², ∞)`), and any Maxwell
  boundary realisation or trace-class statement.
- The correspondence of the symbols with the printed statement of Theorem 14.1 of `16.tex` was not
  re-read in the source, which is not in the repository.

## Verification

- Local, pinned toolchain (Mathlib at `0272bbe1`, cache from `lake exe cache get`): the 7 imported
  repository modules (`FreeEvanescentResolvent20261125`, `RobinDirichletRankOne20261125`,
  `RobinDirichletL2Bounded20261125`, `RobinDirichletPositive20261125`,
  `RobinDirichletInjective20261125`, `RobinDirichletWeakResolvent20261125`,
  `RobinDirichletRealisation20261125`) and the new module compile with exit 0; the new module produces
  no error, warning or `Try this`; its 34 declarations depend only on `propext`, `Classical.choice`,
  `Quot.sound` (25 of the 34 lists wrap over several lines and were parsed as such); the 263 axiom
  reports of the imported modules (39 wrapped) contain only these three. The audit step of the new
  workflow was replayed locally on these logs: `SUCCESS: 34 declarations and 263 imported reports
  ( 39 wrapped lists ); standard axioms only`.
- Certifying run: `.github/workflows/m16-free-evanescent-generator-20261126.yml` (exact-HEAD checkout
  and SHA assertion, pinned toolchain and Mathlib asserted, compilation of the 7 imported modules and of
  the new module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or
  non-standard axiom, artifact with per-declaration axiom lists). The axiom-report regex accepts names
  containing primes (`'(\S+)' depends on axioms`).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
