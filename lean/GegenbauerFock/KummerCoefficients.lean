import Mathlib

/-! V007: algebraic foundation for the unregularized ₁F₁ series.
These lemmas do NOT prove the ultraspherical moment formula nor the
identity with Mathlib's regularized complex hypergeometric function. -/

namespace GegenbauerFock.KummerCoefficients

/-- (1/2)_n/(λ+1)_n, in the standard rising-factorial recurrence. -/
noncomputable def ratio (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ratio lam n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + lam + 1)

@[simp] theorem ratio_zero (lam : ℝ) : ratio lam 0 = 1 := rfl
@[simp] theorem ratio_succ (lam : ℝ) (n : ℕ) :
  ratio lam (n+1) = ratio lam n * ((n : ℝ)+1/2) / ((n : ℝ)+lam+1) := rfl

/-- For positive λ, the ratio is nonnegative and at most one. -/
theorem ratio_bounds (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ ratio lam n ∧ ratio lam n ≤ 1 := by
  induction n with
  | zero => norm_num [ratio]
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) + 1/2 := by positivity
    have hd : 0 < (n : ℝ) + lam + 1 := by positivity
    have hq : ((n : ℝ)+1/2) / ((n : ℝ)+lam+1) ≤ 1 := by
      apply (div_le_one hd).2
      linarith
    rw [ratio_succ]
    constructor
    · exact div_nonneg (mul_nonneg ih.1 hn) hd.le
    · calc
        ratio lam n * ((n : ℝ)+1/2) / ((n : ℝ)+lam+1) =
            ratio lam n * (((n : ℝ)+1/2) / ((n : ℝ)+lam+1)) := by ring
        _ ≤ 1 * (((n : ℝ)+1/2) / ((n : ℝ)+lam+1)) :=
          mul_le_mul_of_nonneg_right ih.2 (div_nonneg hn hd.le)
        _ ≤ 1 := by simpa using hq

theorem ratio_nonneg (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ ratio lam n := (ratio_bounds lam hlam n).1
theorem ratio_le_one (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ratio lam n ≤ 1 := (ratio_bounds lam hlam n).2

/-- The real Kummer series converges for nonnegative arguments. -/
theorem kummerSeries_summable (lam z : ℝ)
    (hlam : 0 < lam) (hz : 0 ≤ z) :
    Summable (fun n : ℕ =>
      ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (ratio_nonneg lam hlam n) (by positivity)
  · intro n
    have ht : 0 ≤ z ^ n / (Nat.factorial n : ℝ) := by positivity
    simpa using
      (mul_le_mul_of_nonneg_right (ratio_le_one lam hlam n) ht)
  · exact Real.summable_pow_div_factorial z

/-- The unregularized scalar Kummer power-series value. -/
noncomputable def kummerSeries (lam z : ℝ) : ℝ :=
  ∑' n : ℕ, ratio lam n * (z ^ n / (Nat.factorial n : ℝ))

#print axioms GegenbauerFock.KummerCoefficients.ratio_bounds
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_summable

end GegenbauerFock.KummerCoefficients
