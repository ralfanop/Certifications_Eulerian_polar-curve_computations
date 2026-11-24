# M16 §13 `eq:mixed-L0-164`, `eq:mixed-L0gap-164`: coefficient-space `L₀ = W_R ⊕ D₃` — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/DiracMaxwellCoefficientModel20261124.lean` (28 declarations).

## Starting point

`DiracMaxwellGraphSpace20261124.mixedBlock_isFredholm_iff_and_index_eq` (#585, in `main`)
proves `thm:dirac-maxwell-obstruction-164` (i)–(ii) for an abstract `L₀ : X →ₗ.[ℂ] X` under
the premises: `L₀` closed, `L₀ : dom L₀ → X` bijective, `‖R₀‖ ≤ 2/3`, `R₀` compact.
The register listed these four premises as open for the concrete `L₀ = W_R ⊕ D₃`.
This file discharges them for the coefficient-space realization of `L₀`.

## Files carried over unchanged from merged stacked PRs

Both PRs were merged into intermediate stacked branches, never into `main`; their
`lean` check runs on the merged heads concluded `success`. The files are added
byte-identical (the workflow re-checks the hashes and re-audits their `#print axioms`):

| File | Source | Check run | SHA-256 |
|---|---|---|---|
| `lean/Manuscript16/V166L2SpectralInverse.lean` | #422 head `0c123675380987d319b2778e253ab9c64f73b8d0` | 135422854632 success | `f7fdb0b544f7bb5c9be5ad83885d6c3b7c4ac518f2a4ee2dcd6c25189d84cab5` |
| `lean/Manuscript16/V166SpectralCutoffs.lean` | #436 head `dfc67dc6128900bea007b0aaf074c9e0dc996ada` | 135542428568 success | `47fd91b90ca0a75336a83821cab632f0c0495f99e2efe8b79a44d98aac827634` |

#422 fixes the spectral list on `ℓ²(MixedIndex, ℂ)` and proves `‖diag(1/λ)‖ = 2/3`;
#436 proves the finite-rank cutoff factorization and the sharp cutoff error.

## What is proved

| Declaration | Statement |
|---|---|
| `cutoff_isCompactOperator` | the finite-rank cutoffs of #436 are compact (factor through `Fin n → ℂ`) |
| `diagonal_isCompactOperator` | `diag(w)` on `ℓ²` is compact if `{i \| ε < ‖wᵢ‖}` is finite for every `ε > 0` (norm limit of cutoffs; Mathlib `isClosed_setOfPred_isCompactOperator`) |
| `multDomain`, `mem_multDomain`, `multOp`, `multOp_apply` | `x ↦ (λᵢ xᵢ)` on the maximal domain `{x ∈ ℓ² \| (λᵢ xᵢ) ∈ ℓ²}`, as a Mathlib `LinearPMap` |
| `mem_graph_multOp_iff`, `multOp_isClosed` | graph `= {(x, y) \| ∀ i, yᵢ = λᵢ xᵢ}`; every maximal-domain multiplication operator is closed |
| `multOp_injective`, `multOp_surjective` | if `λᵢ wᵢ = 1` with `w` bounded: bijective `dom → ℓ²` |
| `ambientResolvent_multOp` | the ambient inverse `R₀` of #585 (open mapping theorem) equals `diag(w)` |
| `maxwellEigen`, `maxwellEigen_eq_sq_sub_sq` | Maxwell eigenvalue `−4k(ℓ+k) = ℓ² − m²`, `ℓ = l+2`, `m = ℓ+2k` (`eq:mixed-maxwell-index-164`) |
| `diracEigen`, `mixedEigen`, `*_eq_inv`, `*_ne_zero`, `mixedEigen_mul_weight` | Dirac eigenvalue `±(n+3/2)`; the weights of #422 are exactly the inverse eigenvalues |
| `maxwell_finite`, `dirac_finite`, `mixedWeight_finite` | for every `ε > 0` only finitely many modes have `‖1/λᵢ‖ > ε` (finite multiplicities included) |
| `mixedInverse_isCompactOperator` | `diag(1/λ)` of #422 is compact |
| `L0`, `L0_apply_maxwell`, `L0_apply_dirac` | `L₀ = W_R ⊕ D₃` on `ℓ²(MixedIndex)`, maximal domain |
| `L0_isClosed`, `L0_injective`, `L0_surjective` | `L₀` closed, bijective `dom L₀ → ℓ²` |
| `L0_ambientResolvent`, `L0_ambientResolvent_norm`, `L0_ambientResolvent_compact` | `R₀ = diag(1/λ)`, `‖R₀‖ = 2/3` (`eq:mixed-L0gap-164`, attained at the Dirac mode `n = 0`), `R₀` compact |
| `coefficientModel_isFredholm_iff_and_index_eq` | for every bounded `E` with `‖E‖ < 3/2` and bounded `A_P, B, C`: `𝒜` Fredholm iff `A_P` Fredholm, and then `ind 𝒜 = ind A_P`; no premise on `L₀` or `R₀` remains |

Local check (pinned toolchain): the nine imported project modules and the new file
compile with exit 0, no warning in the new file; all 28 declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`; the 79 axiom reports printed by the
imported modules contain only these three. Certifying run:
`.github/workflows/m16-dirac-maxwell-coefficient-model-20261124.yml` (exact-HEAD
checkout, pinned toolchain, rebuild of the nine imported modules, hash check of the
carried-over files, `#print axioms` audit, artifacts).

## Scope and residual obligations

This is the spectral (coefficient-space) realization of `L₀`. The unitary
identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` diagonalizing `W_R` and `D₃`
(spectral decomposition of the Maxwell wave operator on the deck-even nonresonant
space; the classical Dirac spectrum `±(n + 3/2)`, multiplicity `(n+1)(n+2)`, of the round
`S³`) is a published input and is NOT formalized. No geometric statement on `S³` is
derived from this file. Still open: `L₀⁻¹ ∈ S_p ⇔ p > 3` (`eq:mixed-schatten-164`) as an
operator statement, and every `det₄` statement (`eq:mixed-det4-164`,
`eq:mixed-det4-criterion-164`).
