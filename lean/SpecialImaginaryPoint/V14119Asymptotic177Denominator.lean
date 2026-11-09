import SpecialImaginaryPoint.V14119Asymptotic177Numerator

/-!
# Manuscript 14.119, equation (177): uniform logarithmic denominator

Uses only the previously kernel-checked explicit sinh and log remainder
bounds. This proves the second-order expansion for log(sinh(x)/x) with an
explicit uniform sixth-order remainder on 0 < x ≤ 1.

The final reciprocal-and-quotient estimate is not asserted here.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

private theorem log_denominator_from_abstract_bounds
    (t A : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAge : t / 6 ≤ A) (hAle : A ≤ t / 5)
    (hE : |A - t / 6 - t ^ 2 / 120| ≤ t ^ 3 / 4410) :
    |Real.log (1 + A) - (t / 6 - t ^ 2 / 180)| ≤ t ^ 3 / 40 := by
  have hA0 : 0 ≤ A := by linarith
  have hAhalf : A ≤ 1 / 2 := by linarith
  have hlog := log_one_add_taylor2 A hA0 hAhalf
  have ht3le : t ^ 3 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t by linarith)]
  have heL := (abs_le.mp hE).1
  have heU := (abs_le.mp hE).2
  have hdelta : A - t / 6 ≤ t ^ 2 / 100 := by
    linarith [ht3le]
  have hsumNonneg : 0 ≤ A + t / 6 := by linarith
  have hsumLe : A + t / 6 ≤ t := by linarith
  have hprod1 :
      (A - t / 6) * (A + t / 6) ≤
        (t ^ 2 / 100) * (A + t / 6) :=
    mul_le_mul_of_nonneg_right hdelta hsumNonneg
  have hprod2 :
      (t ^ 2 / 100) * (A + t / 6) ≤
        (t ^ 2 / 100) * t :=
    mul_le_mul_of_nonneg_left hsumLe (by positivity)
  have hpowNonneg : 0 ≤ A ^ 2 - t ^ 2 / 36 := by
    nlinarith [mul_nonneg
      (show 0 ≤ A - t / 6 by linarith)
      hsumNonneg]
  have hpowLe : A ^ 2 - t ^ 2 / 36 ≤ t ^ 3 / 100 := by
    nlinarith [hprod1, hprod2]
  have hpoly :
      |A - A ^ 2 / 2 - (t / 6 - t ^ 2 / 180)| ≤ t ^ 3 / 150 := by
    have hid :
        A - A ^ 2 / 2 - (t / 6 - t ^ 2 / 180) =
          (A - t / 6 - t ^ 2 / 120) - (A ^ 2 - t ^ 2 / 36) / 2 := by
      ring
    rw [hid]
    apply abs_le.mpr
    constructor
    · nlinarith [heL, hpowLe, pow_nonneg ht0 3]
    · nlinarith [heU, hpowNonneg, pow_nonneg ht0 3]
  have hfacNonneg :
      0 ≤ (t / 5) ^ 2 + (t / 5) * A + A ^ 2 := by positivity
  have hA3le : A ^ 3 ≤ (t / 5) ^ 3 := by
    nlinarith [mul_nonneg
      (show 0 ≤ t / 5 - A by linarith)
      hfacNonneg]
  have hsplit :
      Real.log (1 + A) - (t / 6 - t ^ 2 / 180) =
        (Real.log (1 + A) - (A - A ^ 2 / 2)) +
          (A - A ^ 2 / 2 - (t / 6 - t ^ 2 / 180)) := by ring
  rw [hsplit]
  calc
    |(Real.log (1 + A) - (A - A ^ 2 / 2)) +
        (A - A ^ 2 / 2 - (t / 6 - t ^ 2 / 180))| ≤
      |Real.log (1 + A) - (A - A ^ 2 / 2)| +
        |A - A ^ 2 / 2 - (t / 6 - t ^ 2 / 180)| := abs_add_le _ _
    _ ≤ 2 * A ^ 3 + t ^ 3 / 150 := by linarith [hlog, hpoly]
    _ ≤ t ^ 3 / 40 := by nlinarith [hA3le, pow_nonneg ht0 3]

/-- Actual denominator log(sinh x / x), second order and uniformly bounded. -/
theorem denominator_log_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (Real.sinh x / x) - (x ^ 2 / 6 - x ^ 4 / 180)| ≤
      x ^ 6 / 40 := by
  let t : ℝ := x ^ 2
  let A : ℝ := epsilon x
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1 - x by linarith)]
  have ht2le : t ^ 2 ≤ t := by
    nlinarith [mul_nonneg ht0 (show 0 ≤ 1 - t by linarith)]
  have hAb := epsilon_positive_enclosure x hx hx1
  have hAge : t / 6 ≤ A := by
    simpa only [t, A] using hAb.1
  have hAupper : A ≤ t / 6 + t ^ 2 / 96 := by
    simpa only [t, A] using hAb.2
  have hAle : A ≤ t / 5 := by linarith [hAupper, ht2le]
  have heq :
      A - t / 6 - t ^ 2 / 120 =
        (Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120 := by
    dsimp [A, epsilon, t]
    ring
  have hpow : t ^ 3 / 4410 = x ^ 6 / 4410 := by
    dsimp [t]
    ring
  have hE : |A - t / 6 - t ^ 2 / 120| ≤ t ^ 3 / 4410 := by
    rw [heq, hpow]
    exact epsilon_taylor_bound x hx hx1
  have h := log_denominator_from_abstract_bounds t A ht0 ht1 hAge hAle hE
  have hxne : x ≠ 0 := ne_of_gt hx
  have hratio : Real.sinh x / x = 1 + A := by
    dsimp [A, epsilon]
    field_simp [hxne] <;> ring
  have hlogeq :
      Real.log (Real.sinh x / x) - (x ^ 2 / 6 - x ^ 4 / 180) =
        Real.log (1 + A) - (t / 6 - t ^ 2 / 180) := by
    rw [hratio]
    dsimp [t]
    ring
  have hpow2 : x ^ 6 / 40 = t ^ 3 / 40 := by dsimp [t]; ring
  rw [hlogeq, hpow2]
  exact h

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.denominator_log_taylor

end SpecialImaginaryPoint.V14119Asymptotic177
