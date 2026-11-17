import Mathlib

/-! Arithmetic propagation of order-t^12 Taylor remainders through the exact
Parry quotient. The analytic bounds on P and -PC remain to be discharged. -/

namespace Manuscript14.ParryRemainder

theorem quotient_identity (t β : ℝ) (ht : 0 < t) (hb : 1 < β) :
    Real.log (1 / (β - 1)) / Real.log β =
      ((t / Real.log β) * Real.log (6 / t) -
        (t / Real.log β) * Real.log (6 * (β - 1) / t)) / t := by
  have hβ : 0 < β - 1 := by linarith
  have hl : Real.log (1 / (β - 1)) =
      Real.log (6 / t) - Real.log (6 * (β - 1) / t) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hβ.ne', Real.log_one,
      Real.log_div (by norm_num : (6 : ℝ) ≠ 0) ht.ne',
      Real.log_div (by positivity : (6 : ℝ) * (β - 1) ≠ 0) ht.ne',
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hβ.ne']
    ring
  rw [hl]
  field_simp [ht.ne', (Real.log_pos hb).ne'] <;> ring

theorem propagate (t J P R p r K M : ℝ)
    (ht : 0 < t) (hJ : 1 ≤ J) (hM : 0 ≤ M)
    (hp : |P - p| ≤ K * t ^ 12)
    (hr : |R - r| ≤ M * t ^ 12) :
    |(P * J + R) / t - (p * J + r) / t| ≤
      (K + M) * t ^ 11 * J := by
  have hJ0 : 0 ≤ J := by linarith
  have hsplit : (P * J + R) / t - (p * J + r) / t =
      ((P - p) * J + (R - r)) / t := by
    ring
  have h1 : |(P - p) * J| ≤ K * t ^ 12 * J := by
    rw [abs_mul, abs_of_nonneg hJ0]
    exact mul_le_mul_of_nonneg_right hp hJ0
  have h2 : M * t ^ 12 ≤ M * t ^ 12 * J := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hJ (show 0 ≤ M * t ^ 12 by positivity))
  have hn : |(P - p) * J + (R - r)| ≤ (K + M) * t ^ 12 * J := by
    calc
      _ ≤ |(P - p) * J| + |R - r| := abs_add_le _ _
      _ ≤ K * t ^ 12 * J + M * t ^ 12 * J := add_le_add h1 (hr.trans h2)
      _ = _ := by ring
  rw [hsplit, abs_div, abs_of_pos ht]
  calc
    _ ≤ (K + M) * t ^ 12 * J / t := div_le_div_of_nonneg_right hn ht.le
    _ = _ := by field_simp [ht.ne'] <;> ring

end Manuscript14.ParryRemainder

#print axioms Manuscript14.ParryRemainder.propagate
#print axioms Manuscript14.ParryRemainder.quotient_identity
