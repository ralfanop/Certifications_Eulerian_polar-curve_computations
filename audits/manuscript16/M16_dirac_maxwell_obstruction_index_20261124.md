# M16 §13 `thm:dirac-maxwell-obstruction-164` (i)–(ii): Fredholm property and index — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Lean file:
`lean/Manuscript16/DiracMaxwellObstructionIndex20261124.lean` (15 declarations).
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
Fredholm predicate and index: Mathlib's `ContinuousLinearMap.IsFredholm` (strict map,
closed range, finite-dimensional kernel, finitely generated cokernel, complemented
kernel) and `LinearMap.index = dim ker − dim coker`.

## What is proved

| Declaration | Statement |
|---|---|
| `isFredholm_prodMap_iff` | `diag(F, L) = F.prodMap L` with `L : D ≃L X` is Fredholm iff `F` is (any complete nontrivially normed field) |
| `kerProdMapEquiv` | `ker diag(F, L) ≃ₗ ker F` (the second component of a kernel vector is `0`) |
| `ker_cokerProj`, `cokerProdMapEquiv` | `range diag(F, L) = range F × X`; `coker diag(F, L) ≃ₗ P / range F` |
| `index_prodMap` | `ind diag(F, L) = ind F` |
| `diagonal_eq_prodMap` | the diagonal factor of `V165GraphSchur.typed_factorization` is `F.prodMap L` |
| `block_isFredholm_iff_schur` | `𝒜 = block A_P B C L` is Fredholm iff `F = A_P − B L⁻¹ C` is |
| `block_index_eq_schur` | `ind 𝒜 = ind F` when `F` is Fredholm (via `IsFredholm.index_comp` and index 0 of the two shears) |
| `block_isFredholm_iff_and_index_eq` | if `B L⁻¹ C` is compact and `P` is a complete complex inner-product space: `𝒜` Fredholm iff `A_P` Fredholm, and then `ind 𝒜 = ind A_P` |

The compact-perturbation step reuses `SharedCore.FredholmAtkinson.isFredholm_add_compact_iff`
and `index_add_compact` (PR #469); Atkinson and index stability are not re-proved.

## Premises and residual obligations

The final theorem has exactly two premises besides boundedness of `A_P, B, C`:
the continuous linear equivalence `L : D ≃L X` and the compactness of `B L⁻¹ C`.
It is the abstract typed statement; it does not formalize the concrete mixed
Maxwell–Dirac realization. Still open for the concrete operators: graph space of
`L₀ = W_R ⊕ D₃`, construction of `L` from `L₀` (see the note below), compactness of
`B L⁻¹ C` from the Schatten estimate `eq:mixed-schatten-164`, and every `det₄`
statement (`eq:mixed-det4-164`, `eq:mixed-det4-criterion-164`).

## Relation to earlier work

`V165SchurFredholmIndex.lean` (PR #400) proved kernel/cokernel equivalences with an
ad hoc predicate `HasFredholmData` (closed range, finite kernel and cokernel) and an
ad hoc `fredholmIndex`. PRs #400, #401 (`V165GraphNeumann.lean`, construction of `L`),
#404, #405 and #406 were merged on 18 Nov 2026 into intermediate stacked branches,
not into `main`; their five Lean files are absent from `main`. The present file uses
Mathlib's full `IsFredholm` and does not depend on them.
