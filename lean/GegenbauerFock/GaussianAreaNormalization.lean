import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# V007 — normalized Gaussian area on the complex plane

First measure-theoretic step toward a Gaussian-area Bargmann–Fock
realization. The integration is performed over the genuine Lebesgue
measure on ℂ ≃ ℝ² and uses the pinned Mathlib Gaussian/Gamma theorem.

Neither the full holomorphic Fock isometry nor surjectivity is claimed.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Exact Gaussian integral on ℂ at every positive inverse variance. -/
theorem integral_exp_neg_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) :
    (∫ z : ℂ, Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) =
      Real.pi / alpha := by
  have h := Complex.integral_exp_neg_mul_rpow
    (p := (2 : ℝ)) (b := alpha) (by norm_num) ha
  simpa [Real.Gamma_two, Real.rpow_neg_one, div_eq_mul_inv] using h

/-- The Gaussian area weight α/π has exactly unit mass on ℂ. -/
theorem integral_normalized_gaussian_eq_one
    (alpha : ℝ) (ha : 0 < alpha) :
    (∫ z : ℂ,
      (alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) = 1 := by
  rw [integral_const_mul, integral_exp_neg_norm_sq alpha ha]
  field_simp [ha.ne', Real.pi_ne_zero]

#print axioms GegenbauerFock.GaussianArea.integral_exp_neg_norm_sq
#print axioms GegenbauerFock.GaussianArea.integral_normalized_gaussian_eq_one

end GegenbauerFock.GaussianArea
