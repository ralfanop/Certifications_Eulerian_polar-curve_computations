import GegenbauerFock.GaussianAreaFullIntrinsicReproducing
import GegenbauerFock.FockEvaluationSequence

/-!
# V007 — exact exponential Gaussian growth control of entire L² representatives

On the intrinsic entire Gaussian Fock space, the true point evaluation
agrees at every complex point with the bounded coefficient-space
coherent-state evaluation of the ambient L² projection. The exact
kernel-vector squared norm is exp(alpha * ‖z‖²), providing the
pointwise growth estimate directly in the true Gaussian L² norm.

This is an inequality for genuine analytic representatives, not for
arbitrary equivalence classes of ambient L²(ℂ).
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Pointwise Gaussian Fock growth with the exact squared exponential
weight, for every intrinsic entire Gaussian L² class. -/
theorem intrinsicEntire_pointwise_gaussian_growth_sq
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluation alpha ha z x‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) * ‖x‖ ^ 2 := by
  have hle :
      ‖intrinsicEntireEvaluation alpha ha z x‖ ≤
        ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ := by
    rw [intrinsicEntireEvaluation_eq_projected_full alpha ha x z]
    exact projectedGaussianEvaluation_norm_le alpha ha z
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
  have hnonneg : 0 ≤ ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖intrinsicEntireEvaluation alpha ha z x‖ ^ 2 ≤
        (‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖) ^ 2 := by
          nlinarith [norm_nonneg (intrinsicEntireEvaluation alpha ha z x)]
    _ = Real.exp (alpha * ‖z‖ ^ 2) * ‖x‖ ^ 2 := by
          rw [mul_pow, FockEvaluation.evaluation_norm_sq alpha ha z]

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_pointwise_gaussian_growth_sq

end GegenbauerFock.GaussianArea
