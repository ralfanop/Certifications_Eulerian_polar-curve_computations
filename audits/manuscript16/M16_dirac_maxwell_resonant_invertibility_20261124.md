# M16 §13 `eq:mixed-det4-criterion-164`: operator part of the invertibility criterion — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/DiracMaxwellResonantInvertibility20261124.lean` (14 audited declarations).
Stacked on #588 (`DiracMaxwellCoefficientModel20261124`): the parent of this branch is the #588 head
`26feb5138136e592551caf480c471b08d5dec239`. Independent of #589.

## Starting point

`eq:mixed-det4-criterion-164`: for `μ ≠ 0` the resonant block `𝒜(μ) = [[μ I, B], [C, L₀ + E]]`
is invertible iff `Δ₄(μ) = det₄(I − μ⁻¹ K) ≠ 0` (`eq:mixed-det4-164`), `K = B L⁻¹ C`.
The proof has two steps of different nature:

1. `𝒜(μ)` invertible ⇔ `I − μ⁻¹ K` invertible (Schur reduction and Fredholm alternative for the
   compact `K`): an original step of the manuscript, proved in Lean here;
2. `I + T` invertible ⇔ `det₄(I + T) ≠ 0` for `T ∈ S₄`, applied to `T = −μ⁻¹ K`: published result
   (Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS 2005, Ch. 9, regularized
   determinants `det_n`; the precise theorem number is still to be located in the book), together
   with `K ∈ S₄`.

Already in `main` and not re-proved: `block_bijective_iff`, `block_injective_iff`
(`V165SchurClosedRange`); the Neumann regime `|μ| > ‖B‖‖C‖/(3/2 − ‖E‖)` (`V166ResonantNeumann`);
the Fredholm alternative for a general compact operator (`V166CompactFredholmAlternative`);
`schurCorrection_compact`, `mixedBlock` (#585). The Neumann file covers only large `|μ|`; this file
covers every `μ ≠ 0`.

## What is proved

| Declaration | Statement |
|---|---|
| `shift_eq_smul_normalized` | `μ I − K = μ (I − μ⁻¹ K)`, `μ ≠ 0` |
| `smul_bijective_iff` | `μ T` bijective ⇔ `T` bijective, `μ ≠ 0` |
| `shift_injective_iff_not_hasEigenvalue` | `μ I − K` injective ⇔ `μ` not an eigenvalue of `K` (no compactness) |
| `shift_bijective_iff_not_hasEigenvalue` | `K` compact, `μ ≠ 0`: `μ I − K` bijective ⇔ `μ` not an eigenvalue of `K` (Mathlib Fredholm alternative + bounded inverse theorem) |
| `shift_bijective_iff_injective` | `K` compact, `μ ≠ 0`: `μ I − K` bijective ⇔ injective |
| `normalized_bijective_iff_not_hasEigenvalue` | `K` compact, `μ ≠ 0`: `I − μ⁻¹ K` bijective ⇔ `μ` not an eigenvalue of `K` |
| `resonant_schur_eq` | the Schur map of `𝒜(μ)` is `μ I − K`, `K = B L⁻¹ C` |
| `resonantBlock_bijective_iff_not_hasEigenvalue` | graph space of #585 (closed bijective `L₀`, compact `R₀`, `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2`): `𝒜(μ)` bijective ⇔ `μ` not an eigenvalue of `K` |
| `resonantBlock_bijective_iff_normalized` | same setting: `𝒜(μ)` bijective ⇔ `I − μ⁻¹ K` bijective |
| `resonantBlock_bijective_iff_not_mem_spectrum` | same setting: `𝒜(μ)` bijective ⇔ `μ ∉ σ(K)` |
| `resonantBlock_bijective_iff_injective` | same setting: `𝒜(μ)` bijective ⇔ injective |
| `schurK_eigenspace_finiteDimensional` | same setting: the eigenspace of `K` at `μ ≠ 0` is finite-dimensional |
| `coefficientK_isCompactOperator` | coefficient-space `L₀ = W_R ⊕ D₃` (#588): `K = B L⁻¹ C` compact for every bounded `E` with `‖E‖ < 3/2` and bounded `B, C` |
| `coefficientModel_resonant_invertibility` | **coefficient-space `L₀ = W_R ⊕ D₃`, no premise on `L₀` left: for `μ ≠ 0`, `𝒜(μ)` bijective ⇔ `𝒜(μ)` injective ⇔ `I − μ⁻¹ K` bijective ⇔ `μ` not an eigenvalue of `K` ⇔ `μ ∉ σ(K)`; the eigenspace of `K` at `μ` is finite-dimensional** |

Bijective continuous linear maps between the Banach spaces involved have bounded inverses (open
mapping theorem), so "bijective" is "invertible in `B(P × D(L₀), P × X)`". All statements are on
the actual Hilbert space `P`, the actual graph space `D(L₀)` and `ℓ²(MixedIndex, ℂ)`; no
finite-dimensional surrogate is used.

Local check (pinned toolchain): the eleven imported project modules and the new file compile with
exit 0, no warning in the new file; all 14 declarations depend only on `propext`,
`Classical.choice`, `Quot.sound`; the 112 axiom reports printed by the imported modules contain only
these three. Source SHA-256: `7f11155a0707aad3eecd4a254ebe7ffc1a70972fe7a4267db47acdadca4a9f1f`.
Certifying run: `.github/workflows/m16-dirac-maxwell-resonant-invertibility-20261124.yml`
(exact-HEAD checkout, pinned toolchain, rebuild of the imported modules, `#print axioms` audit,
artifacts).

## Published results cited, not formalized

- Simon 2005, Ch. 9: for `T ∈ S_n`, `det_n(I + T)` is defined and `I + T` is invertible iff
  `det_n(I + T) ≠ 0`. With `n = 4` and `T = −μ⁻¹ K` it turns the Lean equivalence
  `𝒜(μ)` bijective ⇔ `I − μ⁻¹ K` bijective into `eq:mixed-det4-criterion-164`.
- Simon 2005, Ch. 2: `diag(w) ∈ S_p ⇔ w ∈ ℓᵖ` and `S_p` is a two-sided ideal; with #589
  (`w ∈ ℓᵖ ⇔ p > 3`) and `L⁻¹ = L₀⁻¹(I + E L₀⁻¹)⁻¹` this gives `K = B L⁻¹ C ∈ S₄`.
- Mathlib at the pinned commit has no Schatten classes and no regularized determinants; neither
  step above is a Lean theorem here.
- As in #588, the unitary identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` is a published
  input; no geometric statement on `S³` is derived.

## Residual obligations

- Classification of `eq:mixed-det4-164` and of the `det₄` step of `eq:mixed-det4-criterion-164`
  (decision of the scientific lead, as for `eq:feff-det`): published result cited (Simon 2005) or
  open Lean obligation (construction of `S₄` and `det₄` in Lean).
- Discreteness of `σ(K) \ {0}` (Riesz–Schauder theory): not formalized here.
