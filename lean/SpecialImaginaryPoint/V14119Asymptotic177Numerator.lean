import SpecialImaginaryPoint.V14119Asymptotic177Epsilon
import SpecialImaginaryPoint.V14119Asymptotic177Log

/-!
# Manuscript 14.119, equation (177) — logarithmic numerator remainder

The next quantitative result connects the proved sinh remainder to the
first-order logarithmic expansion of its normalized positive factor.
The final reciprocal-of-log and the global quotient bound are separate.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

theorem normalized_epsilon_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |normalizedEpsilon x - x ^ 2 / 20| ≤ x ^ 4 / 735 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have htne : x ^ 2 ≠ 0 := pow_ne_zero _ hxne
  have hfactor :
      normalizedEpsilon x - x ^ 2 / 20 =
        (6 / x ^ 2) *
          ((Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120) := by
    dsimp [normalizedEpsilon, epsilon]
    field_simp [hxne, htne] <;> ring
  rw [hfactor, abs_mul, abs_of_pos (div_pos (by norm_num) (pow_pos hx _))]
  calc
    (6 / x ^ 2) *
        |(Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120| ≤
          (6 / x ^ 2) * (x ^ 6 / 4410) :=
        mul_le_mul_of_nonneg_left (epsilon_taylor_bound x hx hx1) (by positivity)
    _ = x ^ 4 / 735 := by field_simp [hxne, htne] <;> ring

theorem normalized_log_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (1 + normalizedEpsilon x) - x ^ 2 / 20| ≤ x ^ 4 / 100 := by
  let u := normalizedEpsilon x
  have hu := normalized_epsilon_bounds x hx hx1
  have hsqx : x ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1 - x by linarith)]
  have hu_half : u ≤ 1 / 2 := by
    dsimp [u]
    linarith [hu.2]
  have hu_nonneg : 0 ≤ u := hu.1
  have hlog := log_one_add_taylor1 u hu_nonneg hu_half
  have herr := normalized_epsilon_taylor x hx hx1
  have hs_nonneg : 0 ≤ x ^ 2 / 16 + u := by
    nlinarith [hu_nonneg, sq_nonneg x]
  have hsq : u ^ 2 ≤ (x ^ 2 / 16) ^ 2 := by
    nlinarith [mul_nonneg
      (show 0 ≤ x ^ 2 / 16 - u by exact sub_nonneg.mpr hu.2)
      hs_nonneg]
  have hsplit : Real.log (1 + u) - x ^ 2 / 20 =
      (Real.log (1 + u) - u) + (u - x ^ 2 / 20) := by ring
  change |Real.log (1 + u) - x ^ 2 / 20| ≤ x ^ 4 / 100
  rw [hsplit]
  calc
    |(Real.log (1 + u) - u) + (u - x ^ 2 / 20)| ≤
        |Real.log (1 + u) - u| + |u - x ^ 2 / 20| :=
          abs_add_le _ _
    _ ≤ 2 * u ^ 2 + x ^ 4 / 735 := by
      have herr' : |u - x ^ 2 / 20| ≤ x ^ 4 / 735 := herr
      linarith
    _ ≤ x ^ 4 / 100 := by
      nlinarith [hsq]

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.normalized_epsilon_taylor
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.normalized_log_taylor

end SpecialImaginaryPoint.V14119Asymptotic177
