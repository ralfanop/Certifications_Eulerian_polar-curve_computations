import Mathlib

/-!
# V007 — sharp real optimization behind Schatten–Hölder

A reusable entirely real theorem. Assume that a weighted Young
estimate holds at every positive scale:
  2 t N ≤ t² A + B.
Then N² ≤ A B, hence N ≤ √(A B) if N,A,B ≥ 0.

This is the exact scalar minimization step needed to obtain the
optimal product constant 1 from the operator-valued Young inequality.
The zero-energy cases A=0 and N=0 are handled explicitly, without
an invalid division by zero.

This module does not claim the weighted operator estimate: that is
a separate analytic/Lean obligation.
-/

noncomputable section

namespace GegenbauerFock.SchattenYoung

/-- Optimizing a weighted Young inequality over every positive scale
gives the sharp product bound, including the zero-energy cases. -/
theorem all_scales_implies_sq_le_mul
    {a b n : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hy : ∀ t : ℝ, 0 < t → 2 * t * n ≤ t ^ 2 * a + b) :
    n ^ 2 ≤ a * b := by
  by_cases hn0 : n = 0
  · subst n
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using mul_nonneg ha hb
  by_cases ha0 : a = 0
  · have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    have htpos : 0 < b / n + 1 := by positivity
    have hspec := hy (b / n + 1) htpos
    rw [ha0] at hspec
    have hdiv : b / n * n = b := div_mul_cancel₀ b hnpos.ne'
    nlinarith
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    have hspec := hy (n / a) (div_pos hnpos hapos)
    have hh : 2 * (n ^ 2 / a) ≤ n ^ 2 / a + b := by
      calc
        2 * (n ^ 2 / a) = 2 * (n / a) * n := by ring
        _ ≤ (n / a) ^ 2 * a + b := hspec
        _ = n ^ 2 / a + b := by
          field_simp [ha0]
    have hh' := mul_le_mul_of_nonneg_right hh ha
    have hdiv : (n ^ 2 / a) * a = n ^ 2 :=
      div_mul_cancel₀ _ ha0
    nlinarith

/-- Sharp square-root consequence of the scale-invariant Young
inequality. The constant is exactly one, not an upper proxy. -/
theorem all_scales_implies_le_sqrt_mul
    {a b n : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hy : ∀ t : ℝ, 0 < t → 2 * t * n ≤ t ^ 2 * a + b) :
    n ≤ Real.sqrt (a * b) := by
  have hbound : n ^ 2 ≤ a * b :=
    all_scales_implies_sq_le_mul ha hb hn hy
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsq := Real.sq_sqrt hab
  have hroot := Real.sqrt_nonneg (a * b)
  nlinarith

#print axioms GegenbauerFock.SchattenYoung.all_scales_implies_sq_le_mul
#print axioms GegenbauerFock.SchattenYoung.all_scales_implies_le_sqrt_mul

end GegenbauerFock.SchattenYoung
