import Mathlib

/-!
# Manuscript 14.119 (177): uniform Taylor bounds for the real logarithm

These explicit, kernel-checkable bounds for log(1+y) at nonnegative y ≤ 1/2
are deduced from Mathlib's *proved* Taylor remainder theorem.

They are the analytic inputs for the logarithmic numerator and denominator
of the Parry index. No assumption about the final asymptotic formula is used.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

theorem log_one_add_taylor1 (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    |Real.log (1 + y) - y| ≤ 2 * y ^ 2 := by
  have habs : |(-y)| < 1 := by
    rw [abs_neg, abs_of_nonneg hy0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) habs 1
  have hsum :
      (∑ i ∈ Finset.range 1, (-y) ^ (i + 1) / ((i : ℝ) + 1)) = -y := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have hleft : |-y + Real.log (1 + y)| = |Real.log (1 + y) - y| := by
    congr 1
    ring
  rw [hleft, abs_neg, abs_of_nonneg hy0] at h
  have hden : (0 : ℝ) < 1 - y := by linarith
  have hpow : (0 : ℝ) ≤ y ^ 2 := pow_nonneg hy0 _
  have hbound : y ^ 2 / (1 - y) ≤ 2 * y ^ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hpow (show 0 ≤ 1 - 2 * y by linarith)]
  exact h.trans hbound

theorem log_one_add_taylor2 (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * y ^ 3 := by
  have habs : |(-y)| < 1 := by
    rw [abs_neg, abs_of_nonneg hy0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) habs 2
  have hsum :
      (∑ i ∈ Finset.range 2, (-y) ^ (i + 1) / ((i : ℝ) + 1)) =
        -y + y ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hsum] at h
  have hleft :
      |-y + y ^ 2 / 2 + Real.log (1 + y)| =
        |Real.log (1 + y) - (y - y ^ 2 / 2)| := by
    congr 1
    ring
  rw [hleft, abs_neg, abs_of_nonneg hy0] at h
  have hden : (0 : ℝ) < 1 - y := by linarith
  have hpow : (0 : ℝ) ≤ y ^ 3 := pow_nonneg hy0 _
  have hbound : y ^ 3 / (1 - y) ≤ 2 * y ^ 3 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hpow (show 0 ≤ 1 - 2 * y by linarith)]
  exact h.trans hbound

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.log_one_add_taylor1
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.log_one_add_taylor2

end SpecialImaginaryPoint.V14119Asymptotic177
