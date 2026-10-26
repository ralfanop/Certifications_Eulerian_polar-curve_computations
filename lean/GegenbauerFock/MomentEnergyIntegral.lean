import GegenbauerFock.WeightedMoments

/-!
# V007: L² moment energy as a genuine integral

The squared Hilbert norm of the actual n-th monomial Riesz representer
equals the true scalar Lebesgue integral of its pointwise squared norm.
This theorem is the missing bridge between the row-energy series of
the concrete Fock coefficient operator and integral moment formulas.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.MomentEnergyIntegral

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))

include hsupport

theorem monomial_norm_sq_integral (n : ℕ) :
    ‖WeightedMoments.monomial μ hsupport n‖ ^ 2 =
      ∫ u : ℝ, ‖(u : ℂ) ^ n‖ ^ 2 ∂μ := by
  let m := WeightedMoments.monomial μ hsupport n
  have hrep :
      (m : ℝ → ℂ) =ᵐ[μ] (fun u : ℝ => (u : ℂ) ^ n) := by
    simpa [m, WeightedMoments.monomial] using
      (WeightedMoments.monomial_memLp μ hsupport n).coeFn_toLp
  calc
    ‖WeightedMoments.monomial μ hsupport n‖ ^ 2 =
        RCLike.re (inner ℂ m m) := by
          simp [m, inner_self_eq_norm_sq_to_K]
    _ = RCLike.re (∫ u : ℝ, inner ℂ (m u) (m u) ∂μ) := by
          rw [MeasureTheory.L2.inner_def]
    _ = ∫ u : ℝ, ‖(u : ℂ) ^ n‖ ^ 2 ∂μ := by
          rw [← integral_re]
          apply integral_congr_ae
          filter_upwards [hrep] with u hu
          rw [hu, inner_self_eq_norm_sq_to_K]
          simp

#print axioms GegenbauerFock.MomentEnergyIntegral.monomial_norm_sq_integral

end GegenbauerFock.MomentEnergyIntegral
