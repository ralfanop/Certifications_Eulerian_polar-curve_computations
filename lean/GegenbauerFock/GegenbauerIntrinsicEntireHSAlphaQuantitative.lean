import GegenbauerFock.GegenbauerIntrinsicEntireHSStrictMonotonicity

/-!
# V007 — quantitative lower separation in Gaussian scale

The nonnegative Kummer coefficient series has a positive first excited
term. Its monotonicity in the scalar argument has an exact lower gap.
This is stronger than strict monotonicity and is the starting point for
quantitative reconstruction of the Gaussian width alpha.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The gap between positive-argument Kummer masses dominates
the first nonvacuum term even when the lower argument is zero. -/
theorem kummerSeries_argument_first_gap
    (lam s t : ℝ) (hlam : 0 < lam)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ratio lam 1 * (t - s) ≤ kummerSeries lam t - kummerSeries lam s := by
  have ht : 0 ≤ t := le_trans hs hst
  let f₁ : ℕ → ℝ := fun n =>
    ratio lam n * (s ^ n / (Nat.factorial n : ℝ))
  let f₂ : ℕ → ℝ := fun n =>
    ratio lam n * (t ^ n / (Nat.factorial n : ℝ))
  have hs₁ : Summable f₁ := kummerSeries_summable lam s hlam hs
  have hs₂ : Summable f₂ := kummerSeries_summable lam t hlam ht
  have hterm (n : ℕ) : f₁ n ≤ f₂ n := by
    have hpow : s ^ n ≤ t ^ n := by gcongr
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow (by positivity))
      (ratio_nonneg lam hlam n)
  have hs_diff : Summable (fun n => f₂ n - f₁ n) := hs₂.sub hs₁
  have hfirst_le : f₂ 1 - f₁ 1 ≤ ∑' n, (f₂ n - f₁ n) :=
    hs_diff.le_tsum 1 (fun n _ => sub_nonneg.mpr (hterm n))
  have hfirst : f₂ 1 - f₁ 1 = ratio lam 1 * (t - s) := by
    dsimp [f₁, f₂]
    norm_num
    ring
  have hsum :
      (∑' n, (f₂ n - f₁ n)) =
      kummerSeries lam t - kummerSeries lam s := by
    calc
      (∑' n, (f₂ n - f₁ n)) =
          (∑' n, f₂ n) - (∑' n, f₁ n) := hs₂.tsum_sub hs₁
      _ = kummerSeries lam t - kummerSeries lam s := rfl
  calc
    ratio lam 1 * (t - s) = f₂ 1 - f₁ 1 := hfirst.symm
    _ ≤ ∑' n, (f₂ n - f₁ n) := hfirst_le
    _ = kummerSeries lam t - kummerSeries lam s := hsum

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_argument_first_gap

end GegenbauerFock.KummerCoefficients
