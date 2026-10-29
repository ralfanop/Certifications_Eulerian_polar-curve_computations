import Mathlib
import GegenbauerFock.GaussianAreaExplicitTaylorFourierSeries
import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation

/-!
# V007 — sharp Hilbert pointwise bounds on each true normalized Taylor coefficient

Every coefficient of the actual Gaussian Fock Hilbert adjoint is
bounded by the intrinsic Gaussian L² norm. Substituting the
kernel-certified explicit Taylor coefficient formula gives the
corresponding estimate for the normalized analytic derivatives.

The estimate applies to each n and every intrinsic entire Gaussian
L² class; it is not a finite-dimensional polynomial approximation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Each genuine Gaussian-normalized Taylor derivative is bounded
by the full intrinsic Gaussian Fock Hilbert norm. -/
theorem intrinsicEntire_normalized_taylor_coefficient_norm_le
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    ‖monomialWeight alpha n *
      (((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
        iteratedDeriv n (entireRepresentative alpha x) 0)‖ ≤
      ‖x‖ := by
  rw [← coefficientAnalysisL2_intrinsic_eq_scaled_taylor alpha ha x n]
  calc
    ‖coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n‖ ≤
      ‖coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ :=
      lp.norm_apply_le_norm
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (coefficientAnalysisL2 alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) n
    _ = ‖x‖ := coefficientAnalysisL2_norm_intrinsic alpha ha x

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_normalized_taylor_coefficient_norm_le

end GegenbauerFock.GaussianArea
