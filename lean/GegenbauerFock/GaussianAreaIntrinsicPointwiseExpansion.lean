import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation
import GegenbauerFock.GaussianAreaIntrinsicEvaluationContinuous
import GegenbauerFock.FockEvaluationSequence

/-!
# V007 — pointwise coherent series and continuous intrinsic Fock evaluation

The certified intrinsic Gaussian Fock isometry and the full coefficient
reconstruction theorem transport the genuine ℓ² coherent series to
every Gaussian L² vector possessing an entire representative.
No polynomial-density hypothesis is added.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Actual point evaluation of every intrinsic entire Gaussian L²
class equals the infinite coherent Hilbert-series of its genuine
adjoint-analysis coefficients. -/
theorem intrinsicEntire_evaluation_eq_coherent_tsum
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    intrinsicEntireEvaluation alpha ha z x =
      ∑' n : ℕ,
        inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
          ((coefficientAnalysisL2 alpha ha
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) n) := by
  exact (intrinsicEntireEvaluation_eq_coherent_analysis alpha ha x z).trans
    (FockEvaluation.evaluation_eq_tsum_inner alpha ha z _)

/-- The origin evaluates to the zeroth normalized Fock coefficient
of the actual intrinsic entire Gaussian L² vector. -/
theorem intrinsicEntire_evaluation_at_zero_eq_coefficient_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    intrinsicEntireEvaluation alpha ha 0 x =
      (coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) 0 := by
  exact (intrinsicEntireEvaluation_eq_coherent_analysis alpha ha x 0).trans
    (FockEvaluation.evaluation_at_zero alpha ha _)

/-- The previously defined intrinsic continuous point-evaluation
functional agrees with the full Hilbert coefficient reconstruction,
without redefining the same operator. -/
theorem intrinsicEntireEvaluationContinuous_eq_coherent_analysis
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    intrinsicEntireEvaluationContinuous alpha ha z x =
      FockEvaluation.evaluation alpha ha z
        (coefficientAnalysisL2 alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  rw [intrinsicEntireEvaluationContinuous_apply]
  exact intrinsicEntireEvaluation_eq_coherent_analysis alpha ha x z

/-- A pointwise squared Gaussian reproducing bound with the exact
coherent exponential exponent, for every intrinsically entire class. -/
theorem intrinsicEntire_evaluation_sq_le_exp_norm
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluation alpha ha z x‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) * ‖x‖ ^ 2 := by
  have h := intrinsicEntireEvaluation_norm_le_full alpha ha x z
  have hx : 0 ≤ ‖intrinsicEntireEvaluation alpha ha z x‖ := norm_nonneg _
  have hy : 0 ≤ ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq :
      ‖intrinsicEntireEvaluation alpha ha z x‖ ^ 2 ≤
        (‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hy hx)
    nlinarith
  rw [mul_pow, FockEvaluation.evaluation_norm_sq alpha ha z] at hsq
  exact hsq

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_evaluation_eq_coherent_tsum
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_evaluation_at_zero_eq_coefficient_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_eq_coherent_analysis
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_evaluation_sq_le_exp_norm

end GegenbauerFock.GaussianArea
