import GegenbauerFock.GaussianAreaCoefficientSynthesisClosedRange
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — isometric equivalence onto the closed Gaussian polynomial span

An actual surjective Hilbert isometry identifies arbitrary ℓ² Fock
coefficients with the closed normalized-polynomial subspace of
Gaussian-weighted L²(ℂ). This does not identify that closed subspace
with all holomorphic Gaussian-L² functions; the analytic polynomial
density theorem is a separate obligation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The concrete Hilbert subspace obtained by closing Gaussian
holomorphic polynomial vectors in the genuine weighted L² space. -/
noncomputable def gaussianPolynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) :
    Submodule ℂ (Lp ℂ 2 (gaussianAreaMeasure alpha)) :=
  (Submodule.span ℂ (Set.range
    (fun n : ℕ => normalizedMonomialL2Vector alpha ha n))).topologicalClosure

/-- Coefficient synthesis always lies in the closed polynomial span. -/
theorem coefficientSynthesisL2_mem_gaussianPolynomialClosure
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    coefficientSynthesisL2 alpha ha a ∈ gaussianPolynomialClosure alpha ha := by
  change coefficientSynthesisL2 alpha ha a ∈
    (Submodule.span ℂ (Set.range
      (fun n : ℕ => normalizedMonomialL2Vector alpha ha n))).topologicalClosure
  rw [← coefficientSynthesisL2_range_eq_closure_span alpha ha]
  exact ⟨a, rfl⟩

/-- The infinite synthesis is an isometry with target the concrete
Gaussian polynomial closure rather than all weighted L². -/
noncomputable def coefficientSynthesisToPolynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] gaussianPolynomialClosure alpha ha :=
  { toLinearMap :=
      (coefficientSynthesisL2 alpha ha).toLinearMap.codRestrict
        (gaussianPolynomialClosure alpha ha)
        (coefficientSynthesisL2_mem_gaussianPolynomialClosure alpha ha)
    norm_map' := by
      intro a
      change ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖
      exact (coefficientSynthesisL2 alpha ha).norm_map a }

/-- Every element of the concrete polynomial closure is synthesizable
from a square-summable coefficient sequence. -/
theorem coefficientSynthesisToPolynomialClosure_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientSynthesisToPolynomialClosure alpha ha) := by
  intro y
  have hy :
      (y : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact y.property
  obtain ⟨a, ha'⟩ := hy
  refine ⟨a, Subtype.ext ?_⟩
  exact ha'

/-- Surjective linear isometric equivalence of all ℓ² coefficients
onto the closed holomorphic polynomial span in actual Gaussian L². -/
noncomputable def coefficientPolynomialClosureEquiv
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] gaussianPolynomialClosure alpha ha :=
  LinearIsometryEquiv.ofSurjective
    (coefficientSynthesisToPolynomialClosure alpha ha)
    (coefficientSynthesisToPolynomialClosure_surjective alpha ha)

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_mem_gaussianPolynomialClosure
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisToPolynomialClosure_surjective

end GegenbauerFock.GaussianArea
