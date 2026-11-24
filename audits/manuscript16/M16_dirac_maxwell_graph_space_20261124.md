# M16 §13 `thm:dirac-maxwell-obstruction-164` (i)–(ii): graph space of a closed `L₀` — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/DiracMaxwellGraphSpace20261124.lean` (18 declarations).

## Starting point

`DiracMaxwellObstructionIndex20261124.block_isFredholm_iff_and_index_eq` (#576, in
`main`) proves `𝒜` Fredholm iff `A_P` Fredholm and `ind 𝒜 = ind A_P` with two
premises: a continuous linear equivalence `L : D ≃L X` and compactness of `B L⁻¹ C`.
This file discharges the first premise for an abstract closed operator and reduces
the second to compactness of the ambient inverse `R₀` of `L₀`.

## Files carried over unchanged from merged stacked PRs

The Neumann step and the compactness transfer were proved on 18 Nov 2026 in
#401 and #404, which were merged into intermediate stacked branches
(`m16-v165-schur-fredholm-index-20261118`, `m16-v165-graph-neumann-20261118`),
never into `main`. To avoid re-proving them, the two files are added byte-identical
to their merged PR heads:

| File | Source | SHA-256 |
|---|---|---|
| `lean/Manuscript16/V165GraphNeumann.lean` | #401 head `903829959aad06fb03c7772c447b9a13f10e077a` | `847923c079eb0680760b7523dc182b8084deaeac5127dde8cb29d626dccc2d51` |
| `lean/Manuscript16/V166CompactTransfer.lean` | #404 head `8d3a177adf7f24eae101df4c0edc28dce7882621` | `ab8c696a9b5c3dcc60c712d48819b006b9eef78e58038017ff2b56c83686afae` |

Their own `#print axioms` reports are audited by the same workflow. The other files
of the stacked branches (`V165SchurFredholmIndex.lean` with ad hoc
`HasFredholmData`, `V166SchattenIdeal.lean`, `V166RankMinmax.lean`,
`V166HilbertSpectralTransport.lean`, `V166L2SpectralInverse.lean`,
`V166SpectralCutoffs.lean`) are not carried over.

## What is proved

| Declaration | Statement |
|---|---|
| `GraphSpace`, `graphIncl`, `graphOp`, `toGraph` | `D = graph L₀ ⊆ X × X`, `j (x, L₀ x) = x`, realization `(x, L₀ x) ↦ L₀ x` |
| `graphSpace_norm` | `‖(x, L₀ x)‖_D = max ‖x‖ ‖L₀ x‖` (equivalent to `‖x‖ + ‖L₀ x‖`) |
| `exists_toGraph` | every point of `D` is `(x, L₀ x)` with `x ∈ dom L₀` |
| `graphSpace_completeSpace` | `L₀` closed and `X` Banach ⇒ `D` Banach |
| `graphOp_injective`, `graphOp_surjective`, `graphEquiv`, `graphEquiv_apply` | `L₀ : dom L₀ → X` bijective ⇒ `D ≃L X` (open mapping theorem, Mathlib `ContinuousLinearEquiv.ofBijective`) |
| `ambientResolvent_spec` | `R₀ = j ∘ L₀⁻¹ : X →L X`, `R₀ y ∈ dom L₀`, `L₀ (R₀ y) = y` |
| `perturbedGraphEquiv_toGraph` | `L (x, L₀ x) = L₀ x + E x` for the Neumann equivalence `L : D ≃L X` (#401), `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2` |
| `perturbed_solution_iff`, `perturbed_solution_exists` | `x ∈ dom L₀` solves `L₀ x + E x = y` iff `(x, L₀ x) = L⁻¹ y`; existence and uniqueness |
| `perturbed_inverse_graph_norm_le` | `‖L⁻¹ y‖_D ≤ (1 + (1 + ‖E‖)/(3/2 − ‖E‖)) ‖y‖` (graph-norm estimate of `v16_4_section13_graph_domain_schur_20261115.md`) |
| `perturbed_ambientInverse_compact`, `schurCorrection_compact` | `R₀` compact ⇒ `j L⁻¹` compact ⇒ `B j L⁻¹ C` compact (#404) |
| `mixedBlock`, `mixedBlock_apply` | `𝒜 (p, (x, L₀ x)) = (A_P p + B x, C p + L₀ x + E x)` on `P × D → P × X` |
| `mixedBlock_isFredholm_iff_and_index_eq` | `𝒜` Fredholm iff `A_P` Fredholm, and then `ind 𝒜 = ind A_P` |

Local check (pinned toolchain): exit 0, no warnings in the new file; all 18
declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; the 46
axiom reports printed by the six imported modules also contain only these three.
Certifying run: `.github/workflows/m16-dirac-maxwell-graph-space-20261124.yml`
(exact-HEAD checkout, pinned toolchain, rebuild of the six imported modules,
`#print axioms` audit, artifacts).

## Premises and residual obligations

Premises of `mixedBlock_isFredholm_iff_and_index_eq`: `X` complex Banach, `P` complete
complex inner-product space, `L₀ : X →ₗ.[ℂ] X` closed with `L₀ : dom L₀ → X`
bijective, `‖R₀‖ ≤ 2/3`, `R₀` compact, `‖E‖ < 3/2`, `A_P`, `B`, `C` bounded.

This is a statement about an abstract closed operator. It does NOT formalize the
concrete `L₀ = W_R ⊕ D₃`: its closedness, invertibility, `‖R₀‖ = 2/3`, and the
compactness (or Schatten membership, `eq:mixed-schatten-164`) of `R₀` remain open.
The implication Schatten ⇒ compact is classical. No `det₄` statement
(`eq:mixed-det4-164`, `eq:mixed-det4-criterion-164`) is made.
