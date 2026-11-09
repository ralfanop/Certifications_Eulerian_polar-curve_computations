import SpecialImaginaryPoint.V14119Asymptotic177Denominator

/-!
# Manuscript 14.119 equation (177): reciprocal of the logarithmic denominator

The theorem controls the true reciprocal, not a formal Laurent series:
1/log(sinh(x)/x) = 6/x² + 1/5 + O(x²), with a concrete
uniform majorant on 0<x≤1/2.

All use of division below is guarded by strictly positive denominators.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

private theorem reciprocal_denominator_from_error
    (t D : ℝ) (ht : 0 < t) (htSmall : t ≤ 1 / 4)
    (hD : |D - (t / 6 - t ^ 2 / 180)| ≤ t ^ 3 / 40) :
    |1 / D - (6 / t + 1 / 5)| ≤ 2 * t := by
  have htne : t ≠ 0 := ne_of_gt ht
  have ht2le : t ^ 2 ≤ t / 4 := by
    nlinarith [mul_nonneg ht.le (show 0 ≤ 1 / 4 - t by linarith)]
  have ht3first : t ^ 3 ≤ t ^ 2 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 4 - t by linarith)]
  have ht3le : t ^ 3 ≤ t / 16 := by linarith [ht3first, ht2le]
  have hDlower := (abs_le.mp hD).1
  have hDpos : 0 < D := by linarith [ht2le, ht3le]
  have hDne : D ≠ 0 := ne_of_gt hDpos

  let v : ℝ := 6 * D / t - 1
  have hveq :
      v + t / 30 = (6 / t) * (D - (t / 6 - t ^ 2 / 180)) := by
    dsimp [v]
    field_simp [htne] <;> ring
  have hve : |v + t / 30| ≤ 3 * t ^ 2 / 20 := by
    rw [hveq, abs_mul, abs_of_pos (div_pos (by norm_num) ht)]
    calc
      (6 / t) * |D - (t / 6 - t ^ 2 / 180)| ≤
          (6 / t) * (t ^ 3 / 40) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 3 * t ^ 2 / 20 := by field_simp [htne] <;> ring
  have hvAbs : |v| ≤ t / 10 := by
    have heq : v = (v + t / 30) - t / 30 := by ring
    rw [heq]
    calc
      |(v + t / 30) - t / 30| ≤ |v + t / 30| + |t / 30| :=
        abs_sub_le _ _
      _ ≤ 3 * t ^ 2 / 20 + t / 30 := by
        rw [abs_of_pos (show 0 < t / 30 by positivity)]
        linarith [hve]
      _ ≤ t / 10 := by linarith [ht2le]
  have h1vhalf : (1 / 2 : ℝ) ≤ 1 + v := by
    have hlow := (abs_le.mp hvAbs).1
    linarith
  have h1vpos : 0 < 1 + v := by linarith
  have hfactor : D = (t / 6) * (1 + v) := by
    dsimp [v]
    field_simp [htne] <;> ring
  let w : ℝ := (v + t / 30) + v * (t / 30)
  have hrec :
      1 / D - (6 / t + 1 / 5) = -(6 / t) * w / (1 + v) := by
    rw [hfactor]
    dsimp [w]
    field_simp [htne, ne_of_gt h1vpos] <;> ring
  have hwprod : |v * (t / 30)| ≤ t ^ 2 / 300 := by
    rw [abs_mul, abs_of_pos (show 0 < t / 30 by positivity)]
    calc
      |v| * (t / 30) ≤ (t / 10) * (t / 30) :=
        mul_le_mul_of_nonneg_right hvAbs (by positivity)
      _ = t ^ 2 / 300 := by ring
  have hw : |w| ≤ 23 * t ^ 2 / 150 := by
    calc
      |w| ≤ |v + t / 30| + |v * (t / 30)| := by
        dsimp [w]
        exact abs_add_le _ _
      _ ≤ 3 * t ^ 2 / 20 + t ^ 2 / 300 := add_le_add hve hwprod
      _ = 23 * t ^ 2 / 150 := by ring
  have hfrac : |w| / (1 + v) ≤ 2 * |w| := by
    apply (div_le_iff₀ h1vpos).2
    nlinarith [mul_nonneg (abs_nonneg w)
      (show 0 ≤ 2 * (1 + v) - 1 by linarith)]
  have hAbsEq :
      |1 / D - (6 / t + 1 / 5)| =
        (6 / t) * (|w| / (1 + v)) := by
    rw [hrec, abs_div, abs_mul, abs_neg,
      abs_of_pos (div_pos (by norm_num) ht), abs_of_pos h1vpos]
    ring
  rw [hAbsEq]
  calc
    (6 / t) * (|w| / (1 + v)) ≤ (6 / t) * (2 * |w|) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ ≤ (6 / t) * (2 * (23 * t ^ 2 / 150)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hw (by norm_num))
        (by positivity)
    _ = (46 / 25 : ℝ) * t := by field_simp [htne] <;> ring
    _ ≤ 2 * t := by linarith

theorem reciprocal_denominator_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1 / 2) :
    |1 / Real.log (Real.sinh x / x) - (6 / x ^ 2 + 1 / 5)| ≤
      2 * x ^ 2 := by
  let t : ℝ := x ^ 2
  let D : ℝ := Real.log (Real.sinh x / x)
  have ht : 0 < t := by dsimp [t]; positivity
  have htSmall : t ≤ 1 / 4 := by
    dsimp [t]
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1 / 2 - x by linarith)]
  have hx1' : x ≤ 1 := by linarith
  have hDeq :
      D - (t / 6 - t ^ 2 / 180) =
        Real.log (Real.sinh x / x) - (x ^ 2 / 6 - x ^ 4 / 180) := by
    dsimp [D, t]
    ring
  have hpow : t ^ 3 / 40 = x ^ 6 / 40 := by dsimp [t]; ring
  have hD : |D - (t / 6 - t ^ 2 / 180)| ≤ t ^ 3 / 40 := by
    rw [hDeq, hpow]
    exact denominator_log_taylor x hx hx1'
  have h := reciprocal_denominator_from_error t D ht htSmall hD
  exact h

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.reciprocal_denominator_taylor

end SpecialImaginaryPoint.V14119Asymptotic177
