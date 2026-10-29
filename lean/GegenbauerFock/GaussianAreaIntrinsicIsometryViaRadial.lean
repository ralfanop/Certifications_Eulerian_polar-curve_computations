import GegenbauerFock.GaussianAreaEntireRadialCoefficientDensity
import GegenbauerFock.GaussianAreaPolynomialClosureEquiv

/-!
# V007 — full intrinsic Bargmann–Fock isometry from genuine radial moments

This independent proof route relies on the actual planar Gaussian L²
monomial coefficients, their radial-circle representation, radial Gamma
moments, and complex Taylor uniqueness. In particular, it does not
postulate polynomial density, nor does it identify the intrinsic entire
Gaussian space with the closure of polynomials by definition.

The resulting map is onto the independently defined submodule of
Gaussian L² classes with entire representatives, not onto all L²(ℂ).
These declarations are candidates pending an exact-SHA Lean axiom audit.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Actual normalized monomial synthesis, with codomain the intrinsic
entire-representative Gaussian Hilbert subspace, is an isometry. -/
noncomputable def coefficientSynthesisIntrinsicViaRadial
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  { toLinearMap :=
      (coefficientSynthesisL2 alpha ha).toLinearMap.codRestrict
        (entireGaussianL2Submodule alpha)
        (fun a =>
          gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha
            (coefficientSynthesisL2_mem_gaussianPolynomialClosure alpha ha a))
    norm_map' := by
      intro a
      change ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖
      exact (coefficientSynthesisL2 alpha ha).norm_map a }

/-- The genuine radial/Taylor moment uniqueness theorem makes the
coefficient synthesis onto every intrinsic entire Gaussian L² class. -/
theorem coefficientSynthesisIntrinsicViaRadial_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientSynthesisIntrinsicViaRadial alpha ha) := by
  intro x
  have hx :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha :=
    (intrinsicEntire_le_polynomialClosure_via_radial_inner alpha ha) x.property
  have hrange :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hx
  obtain ⟨a, ha'⟩ := hrange
  refine ⟨a, Subtype.ext ?_⟩
  exact ha'

/-- The complete Bargmann–Fock isometric equivalence between normalized
square-summable Taylor coefficients and intrinsically entire Gaussian L². -/
noncomputable def coefficientIntrinsicFockEquivViaRadial
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  LinearIsometryEquiv.ofSurjective
    (coefficientSynthesisIntrinsicViaRadial alpha ha)
    (coefficientSynthesisIntrinsicViaRadial_surjective alpha ha)

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisIntrinsicViaRadial_surjective
#print axioms GegenbauerFock.GaussianArea.coefficientIntrinsicFockEquivViaRadial

end GegenbauerFock.GaussianArea
