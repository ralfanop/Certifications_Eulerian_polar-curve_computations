import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Manuscript16.V165SchurClosedRange
import Manuscript16.DiracMaxwellCoefficientModel20261124

/-!
# M16 §13, `eq:mixed-det4-criterion-164`: operator part of the invertibility criterion

`eq:mixed-det4-criterion-164` states that, for `μ ≠ 0`, the resonant mixed block
`𝒜(μ) = [[μ I, B], [C, L₀ + E]]` is invertible iff `Δ₄(μ) = det₄(I − μ⁻¹ K) ≠ 0`, with the
Schur correction `K = B L⁻¹ C`. Its proof has two steps:

1. (original, proved here) `𝒜(μ)` is invertible iff `I − μ⁻¹ K` is invertible, iff `μ` is not
   an eigenvalue of `K`, iff `μ ∉ σ(K)`, iff `𝒜(μ)` is injective; the eigenspace of `K` at `μ`
   is finite-dimensional;
2. (published result cited, not formalized) for `T ∈ S₄`, `I + T` is invertible iff
   `det₄(I + T) ≠ 0` (Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS 2005, Ch. 9),
   applied to `T = −μ⁻¹ K`, together with `K ∈ S₄`.

This file proves step 1 for the abstract graph space of #585 (closed bijective `L₀`, compact
`R₀`, `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2`) and specializes it, with no premise on `L₀` left, to the
coefficient-space `L₀ = W_R ⊕ D₃` of #588. Only bounded operators on the actual Hilbert space
`P` and the actual graph space `D(L₀)` are used; no finite-dimensional surrogate.

Inputs from Mathlib: the Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`, `hasEigenvalue_iff_mem_spectrum`), the
bounded inverse theorem (`ContinuousLinearMap.isUnit_iff_bijective`) and finite dimensionality of
the nonzero eigenspaces of a compact operator (`ContinuousLinearMap.finite_dimensional_eigenspace`).

NOT formalized here: the Schatten ideal `S₄`, the membership `K ∈ S₄`, the regularized
determinant `det₄` and its zero criterion (Mathlib at the pinned commit has no Schatten classes);
the discreteness of `σ(K) \ {0}` (Riesz–Schauder theory); the unitary identification of
`ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)`. No geometric statement on `S³` is derived.
-/

noncomputable section

namespace Manuscript16.DiracMaxwellResonantInvertibility20261124

open Module End
open Manuscript16.V165GraphSchur
open Manuscript16.DiracMaxwellObstructionIndex20261124
open Manuscript16.DiracMaxwellGraphSpace20261124
open Manuscript16.DiracMaxwellCoefficientModel20261124
open Manuscript16.V166L2SpectralInverse

section Shift

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- `μ I − K = μ (I − μ⁻¹ K)` for `μ ≠ 0`. -/
theorem shift_eq_smul_normalized (K : P →L[ℂ] P) {μ : ℂ} (hμ : μ ≠ 0) :
    μ • (1 : P →L[ℂ] P) - K = μ • ((1 : P →L[ℂ] P) - μ⁻¹ • K) := by
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hμ, one_smul]

/-- For `μ ≠ 0`, `μ T` is bijective iff `T` is bijective. -/
theorem smul_bijective_iff (T : P →L[ℂ] P) {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (μ • T) ↔ Function.Bijective T := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun x y h => hi ?_, fun y => ?_⟩
    · change μ • T x = μ • T y
      rw [h]
    · obtain ⟨x, hx⟩ := hs (μ • y)
      exact ⟨x, smul_right_injective P hμ (show μ • T x = μ • y from hx)⟩
  · rintro ⟨hi, hs⟩
    refine ⟨fun x y h => hi (smul_right_injective P hμ (show μ • T x = μ • T y from h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hs (μ⁻¹ • y)
    refine ⟨x, ?_⟩
    change μ • T x = y
    rw [hx, smul_smul, mul_inv_cancel₀ hμ, one_smul]

/-- Injectivity of `μ I − K` is the absence of the eigenvalue `μ` (no compactness used). -/
theorem shift_injective_iff_not_hasEigenvalue (K : P →L[ℂ] P) (μ : ℂ) :
    Function.Injective (μ • (1 : P →L[ℂ] P) - K) ↔ ¬ HasEigenvalue (K : End ℂ P) μ := by
  rw [hasEigenvalue_iff, not_not]
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : (K : End ℂ P) x = μ • x := mem_eigenspace_iff.mp hx
    apply h
    change μ • x - K x = μ • (0 : P) - K 0
    rw [show K x = μ • x from hx', sub_self, smul_zero, map_zero, sub_zero]
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx0 : μ • x - K x = 0 := hx
    have hx' : x ∈ eigenspace (K : End ℂ P) μ := by
      rw [mem_eigenspace_iff]
      exact (sub_eq_zero.mp hx0).symm
    rw [h] at hx'
    exact (Submodule.mem_bot ℂ).mp hx'

variable [CompleteSpace P]

/-- Fredholm alternative in bijective form: for compact `K` and `μ ≠ 0`, `μ I − K` is
bijective iff `μ` is not an eigenvalue of `K`. -/
theorem shift_bijective_iff_not_hasEigenvalue (K : P →L[ℂ] P) (hK : IsCompactOperator K)
    {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (μ • (1 : P →L[ℂ] P) - K) ↔ ¬ HasEigenvalue (K : End ℂ P) μ := by
  constructor
  · exact fun h => (shift_injective_iff_not_hasEigenvalue K μ).1 h.1
  · intro h
    have hres : μ ∈ resolventSet ℂ K :=
      (hK.hasEigenvalue_or_mem_resolventSet hμ).resolve_left h
    rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hres

/-- For compact `K` and `μ ≠ 0`, `μ I − K` is bijective iff it is injective. -/
theorem shift_bijective_iff_injective (K : P →L[ℂ] P) (hK : IsCompactOperator K)
    {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (μ • (1 : P →L[ℂ] P) - K) ↔
      Function.Injective (μ • (1 : P →L[ℂ] P) - K) :=
  (shift_bijective_iff_not_hasEigenvalue K hK hμ).trans
    (shift_injective_iff_not_hasEigenvalue K μ).symm

/-- For compact `K` and `μ ≠ 0`, `I − μ⁻¹ K` is bijective iff `μ` is not an eigenvalue of `K`. -/
theorem normalized_bijective_iff_not_hasEigenvalue (K : P →L[ℂ] P) (hK : IsCompactOperator K)
    {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective ((1 : P →L[ℂ] P) - μ⁻¹ • K) ↔ ¬ HasEigenvalue (K : End ℂ P) μ := by
  rw [← smul_bijective_iff _ hμ, ← shift_eq_smul_normalized K hμ]
  exact shift_bijective_iff_not_hasEigenvalue K hK hμ

end Shift

section Block

variable {P X : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The Schur correction `K = B L⁻¹ C : P →L P` of the mixed block, `L = L₀ + E`. -/
abbrev schurK (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X) : P →L[ℂ] P :=
  schurCorrection (B.comp (graphIncl L₀)) C (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)

omit [CompleteSpace P] in
/-- The Schur map of the resonant block `𝒜(μ)` is `F = μ I − K`. -/
theorem resonant_schur_eq (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X) (μ : ℂ) :
    schur (μ • (1 : P →L[ℂ] P)) (B.comp (graphIncl L₀)) C
        (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE) =
      μ • (1 : P →L[ℂ] P) - schurK L₀ hcl hinj hsurj E hG hE B C :=
  rfl

/-- `eq:mixed-det4-criterion-164`, operator part, abstract graph space: for compact `R₀` and
`μ ≠ 0`, `𝒜(μ)` is bijective iff `μ` is not an eigenvalue of `K = B L⁻¹ C`. -/
theorem resonantBlock_bijective_iff_not_hasEigenvalue (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (mixedBlock L₀ hcl hinj hsurj E hG hE (μ • (1 : P →L[ℂ] P)) B C) ↔
      ¬ HasEigenvalue (schurK L₀ hcl hinj hsurj E hG hE B C : End ℂ P) μ := by
  have hK := schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt
  unfold mixedBlock
  rw [block_bijective_iff, resonant_schur_eq]
  exact shift_bijective_iff_not_hasEigenvalue _ hK hμ

/-- Abstract graph space: for `μ ≠ 0`, `𝒜(μ)` is bijective iff `I − μ⁻¹ K` is bijective. -/
theorem resonantBlock_bijective_iff_normalized (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (mixedBlock L₀ hcl hinj hsurj E hG hE (μ • (1 : P →L[ℂ] P)) B C) ↔
      Function.Bijective
        ((1 : P →L[ℂ] P) - μ⁻¹ • schurK L₀ hcl hinj hsurj E hG hE B C) :=
  (resonantBlock_bijective_iff_not_hasEigenvalue L₀ hcl hinj hsurj E hG hE B C hcpt hμ).trans
    (normalized_bijective_iff_not_hasEigenvalue _
      (schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt) hμ).symm

/-- Abstract graph space: for `μ ≠ 0`, `𝒜(μ)` is bijective iff `μ ∉ σ(K)`. -/
theorem resonantBlock_bijective_iff_not_mem_spectrum (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (mixedBlock L₀ hcl hinj hsurj E hG hE (μ • (1 : P →L[ℂ] P)) B C) ↔
      μ ∉ spectrum ℂ (schurK L₀ hcl hinj hsurj E hG hE B C) :=
  (resonantBlock_bijective_iff_not_hasEigenvalue L₀ hcl hinj hsurj E hG hE B C hcpt hμ).trans
    ((schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt).hasEigenvalue_iff_mem_spectrum
      hμ).not

/-- Abstract graph space: for `μ ≠ 0`, `𝒜(μ)` is bijective iff it is injective. -/
theorem resonantBlock_bijective_iff_injective (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (mixedBlock L₀ hcl hinj hsurj E hG hE (μ • (1 : P →L[ℂ] P)) B C) ↔
      Function.Injective (mixedBlock L₀ hcl hinj hsurj E hG hE (μ • (1 : P →L[ℂ] P)) B C) := by
  have hK := schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt
  unfold mixedBlock
  rw [block_bijective_iff, block_injective_iff, resonant_schur_eq]
  exact shift_bijective_iff_injective _ hK hμ

/-- Abstract graph space: the eigenspace of `K` at `μ ≠ 0` is finite-dimensional. -/
theorem schurK_eigenspace_finiteDimensional (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (schurK L₀ hcl hinj hsurj E hG hE B C).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt) μ hμ

end Block

section CoefficientModel

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- `K = B L⁻¹ C` for the coefficient-space `L = L₀ + E`, `L₀ = W_R ⊕ D₃` (#588). -/
abbrev coefficientK (E : L2 MixedIndex →L[ℂ] L2 MixedIndex) (hE : ‖E‖ < (3 : ℝ) / 2)
    (B : L2 MixedIndex →L[ℂ] P) (C : P →L[ℂ] L2 MixedIndex) : P →L[ℂ] P :=
  schurK L0 L0_isClosed L0_injective L0_surjective E L0_ambientResolvent_norm.le hE B C

/-- The resonant block `𝒜(μ)` of the coefficient-space model. -/
abbrev coefficientBlock (E : L2 MixedIndex →L[ℂ] L2 MixedIndex) (hE : ‖E‖ < (3 : ℝ) / 2)
    (B : L2 MixedIndex →L[ℂ] P) (C : P →L[ℂ] L2 MixedIndex) (μ : ℂ) :=
  mixedBlock L0 L0_isClosed L0_injective L0_surjective E L0_ambientResolvent_norm.le hE
    (μ • (1 : P →L[ℂ] P)) B C

omit [CompleteSpace P] in
/-- For the coefficient-space `L₀ = W_R ⊕ D₃`, `K = B L⁻¹ C` is compact for every bounded
`E` with `‖E‖ < 3/2` and bounded `B, C`. -/
theorem coefficientK_isCompactOperator (E : L2 MixedIndex →L[ℂ] L2 MixedIndex)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : L2 MixedIndex →L[ℂ] P) (C : P →L[ℂ] L2 MixedIndex) :
    IsCompactOperator (coefficientK E hE B C) :=
  schurCorrection_compact L0 L0_isClosed L0_injective L0_surjective E
    L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact

/-- `eq:mixed-det4-criterion-164`, operator part, for the coefficient-space
`L₀ = W_R ⊕ D₃`, with no premise on `L₀` left: for every bounded `E` with `‖E‖ < 3/2`,
bounded `B, C` and `μ ≠ 0`, the following are equivalent:
`𝒜(μ)` bijective; `𝒜(μ)` injective; `I − μ⁻¹ K` bijective; `μ` is not an eigenvalue of `K`;
`μ ∉ σ(K)`. Moreover the eigenspace of `K` at `μ` is finite-dimensional. -/
theorem coefficientModel_resonant_invertibility (E : L2 MixedIndex →L[ℂ] L2 MixedIndex)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : L2 MixedIndex →L[ℂ] P) (C : P →L[ℂ] L2 MixedIndex)
    {μ : ℂ} (hμ : μ ≠ 0) :
    (Function.Bijective (coefficientBlock E hE B C μ) ↔
        Function.Injective (coefficientBlock E hE B C μ)) ∧
      (Function.Bijective (coefficientBlock E hE B C μ) ↔
        Function.Bijective ((1 : P →L[ℂ] P) - μ⁻¹ • coefficientK E hE B C)) ∧
      (Function.Bijective (coefficientBlock E hE B C μ) ↔
        ¬ HasEigenvalue (coefficientK E hE B C : End ℂ P) μ) ∧
      (Function.Bijective (coefficientBlock E hE B C μ) ↔
        μ ∉ spectrum ℂ (coefficientK E hE B C)) ∧
      FiniteDimensional ℂ (eigenspace (coefficientK E hE B C).toLinearMap μ) :=
  ⟨resonantBlock_bijective_iff_injective L0 L0_isClosed L0_injective L0_surjective E
      L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact hμ,
    resonantBlock_bijective_iff_normalized L0 L0_isClosed L0_injective L0_surjective E
      L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact hμ,
    resonantBlock_bijective_iff_not_hasEigenvalue L0 L0_isClosed L0_injective L0_surjective E
      L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact hμ,
    resonantBlock_bijective_iff_not_mem_spectrum L0 L0_isClosed L0_injective L0_surjective E
      L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact hμ,
    schurK_eigenspace_finiteDimensional L0 L0_isClosed L0_injective L0_surjective E
      L0_ambientResolvent_norm.le hE B C L0_ambientResolvent_compact hμ⟩

end CoefficientModel

end Manuscript16.DiracMaxwellResonantInvertibility20261124

#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.shift_eq_smul_normalized
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.smul_bijective_iff
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.shift_injective_iff_not_hasEigenvalue
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.shift_bijective_iff_not_hasEigenvalue
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.shift_bijective_iff_injective
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.normalized_bijective_iff_not_hasEigenvalue
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.resonant_schur_eq
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.resonantBlock_bijective_iff_not_hasEigenvalue
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.resonantBlock_bijective_iff_normalized
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.resonantBlock_bijective_iff_not_mem_spectrum
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.resonantBlock_bijective_iff_injective
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.schurK_eigenspace_finiteDimensional
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.coefficientK_isCompactOperator
#print axioms Manuscript16.DiracMaxwellResonantInvertibility20261124.coefficientModel_resonant_invertibility
