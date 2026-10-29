import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaCoherentIntrinsicAgreement

/-!
# V007 — constructive coefficient reconstruction and evaluation on the full
intrinsic Gaussian Bargmann–Fock Hilbert space

The full polynomial-density / onto theorem has been kernel-certified.
We now show that the already defined *ambient Hilbert adjoint* of
coefficient synthesis genuinely reconstructs every intrinsic entire
Gaussian L² vector, pointwise via its coherent entire series.

This is not a claim of reconstruction on all Gaussian L²(ℂ).
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Hilbert adjoint coefficient analysis is a genuine two-sided inverse
of synthesis on *all intrinsic entire* Gaussian L² vectors, without
requiring a coefficient-space membership assumption. -/
theorem coefficientSynthesis_analysis_eq_intrinsic
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    coefficientSynthesisL2 alpha ha
      (coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) =
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  obtain ⟨a, h⟩ := intrinsicEntire_exists_coefficient_synthesis alpha ha x
  rw [← h, coefficientAnalysisL2_synthesis]

/-- The intrinsic entire representative at *every* complex point is
exactly the coherent Bargmann–Fock series of its true Hilbert-adjoint
coefficient sequence. -/
theorem intrinsicEntireEvaluation_eq_coherent_analysis
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    intrinsicEntireEvaluation alpha ha z x =
      FockEvaluation.evaluation alpha ha z
        (coefficientAnalysisL2 alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  obtain ⟨a, h⟩ := intrinsicEntire_exists_coefficient_synthesis alpha ha x
  have hx : x = synthesizedIntrinsicVector alpha ha a := by
    apply Subtype.ext
    exact h.symm
  subst x
  change intrinsicEntireEvaluation alpha ha z
      (synthesizedIntrinsicVector alpha ha a) =
    FockEvaluation.evaluation alpha ha z
      (coefficientAnalysisL2 alpha ha
        (coefficientSynthesisL2 alpha ha a))
  rw [coefficientAnalysisL2_synthesis]
  exact intrinsicEntireEvaluation_synthesized alpha ha a z

/-- Coefficient analysis preserves the *entire intrinsic* Gaussian
L² norm, not just the norm on the previously defined polynomial span. -/
theorem coefficientAnalysisL2_norm_intrinsic
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ‖coefficientAnalysisL2 alpha ha
       (x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ = ‖x‖ := by
  calc
    ‖coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ =
      ‖coefficientSynthesisL2 alpha ha
        (coefficientAnalysisL2 alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))‖ :=
      ((coefficientSynthesisL2 alpha ha).norm_map _).symm
    _ = ‖x‖ := by
      rw [coefficientSynthesis_analysis_eq_intrinsic alpha ha x]
      rfl

/-- The coherent-state evaluation estimate extends to the entire
intrinsic holomorphic Gaussian L² space, with its genuine L² norm. -/
theorem intrinsicEntireEvaluation_norm_le_full
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluation alpha ha z x‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ := by
  have hx :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha :=
    intrinsicEntire_le_polynomialClosure_unconditional alpha ha x.property
  simpa only [] using
    intrinsicEntireEvaluation_norm_le_on_polynomialClosure alpha ha z
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) hx

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesis_analysis_eq_intrinsic
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_eq_coherent_analysis
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_norm_intrinsic
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_norm_le_full

end GegenbauerFock.GaussianArea
