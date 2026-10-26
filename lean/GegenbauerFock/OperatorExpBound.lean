import GegenbauerFock.ConcreteFockOperator
import GegenbauerFock.GeneralUltrasphericalFock

/-!
# V007: Gaussian exponential majorant for the actual bounded Fock operator

For each probability measure supported on [-1,1] and α>0,
the concrete factorial-moment Hilbert analysis operator has squared
output norm bounded by exp(1/(4α)) times the squared L² input norm.

This is a bound on the *specific* infinite-dimensional operator,
not merely a conditional operator-norm estimate for an abstract map.
-/

open MeasureTheory

namespace GegenbauerFock.ConcreteFock

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
variable (alpha : ℝ) (ha : 0 < alpha)

include hsupport ha

theorem sum_squared_rows_le_exp :
    (∑' n, ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2) ≤
      Real.exp (1 / (4 * alpha)) := by
  have hs := WeightedMoments.coefficient_norm_sq_summable
    μ hsupport alpha ha
  have hb := hs.tsum_le_tsum
    (WeightedMoments.coefficient_norm_sq_le μ hsupport alpha ha)
    (WeightedMoments.squareWeight_summable alpha)
  have hexp :
      (∑' n, WeightedMoments.squareWeight alpha n) =
        Real.exp (1 / (4 * alpha)) := by
    change (∑' n : ℕ, (1 / (4 * alpha)) ^ n /
      (Nat.factorial n : ℝ)) = Real.exp (1 / (4 * alpha))
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact hb.trans_eq hexp

theorem operator_norm_sq_le_exp (f : Lp ℂ 2 μ) :
    ‖operator μ hsupport alpha ha f‖ ^ 2 ≤
      Real.exp (1 / (4 * alpha)) * ‖f‖ ^ 2 := by
  calc
    ‖operator μ hsupport alpha ha f‖ ^ 2 ≤
        (∑' n, ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2) *
          ‖f‖ ^ 2 :=
      operator_norm_sq_bound μ hsupport alpha ha f
    _ ≤ Real.exp (1 / (4 * alpha)) * ‖f‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (sum_squared_rows_le_exp μ hsupport alpha ha)
        (sq_nonneg _)

/-- Explicit Gaussian bound for the full operator norm, not just
for its action on individual input functions. -/
theorem operator_norm_le_sqrt_exp :
    ‖operator μ hsupport alpha ha‖ ≤
      Real.sqrt (Real.exp (1 / (4 * alpha))) := by
  apply ContinuousLinearMap.opNorm_le_bound
    _ (Real.sqrt_nonneg _)
  intro f
  have hsq := operator_norm_sq_le_exp μ hsupport alpha ha f
  have hr : (Real.sqrt (Real.exp (1 / (4 * alpha)))) ^ 2 =
      Real.exp (1 / (4 * alpha)) :=
    Real.sq_sqrt (le_of_lt (Real.exp_pos _))
  have hp : 0 ≤ Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖f‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hn : 0 ≤ ‖operator μ hsupport alpha ha f‖ := norm_nonneg _
  change ‖operator μ hsupport alpha ha f‖ ≤
    Real.sqrt (Real.exp (1 / (4 * alpha))) * ‖f‖
  nlinarith [sq_nonneg ‖f‖]

#print axioms GegenbauerFock.ConcreteFock.sum_squared_rows_le_exp
#print axioms GegenbauerFock.ConcreteFock.operator_norm_sq_le_exp
#print axioms GegenbauerFock.ConcreteFock.operator_norm_le_sqrt_exp

end GegenbauerFock.ConcreteFock
