import GegenbauerFock.KummerPositiveBounds

/-!
# V007 — strictly positive first nonvacuum term in the true Kummer mass

In the unregularized convergent Kummer series with λ>0 and z≥0,
the n=0 term is 1 and the n=1 term is ratio(λ,1)*z.
All remaining terms are nonnegative. Thus this explicit first-order
correction is a rigorous *lower* bound, complementing the independently
certified exponential *upper* bound. It implies K(λ,z)>1 for z>0.

No analytic asymptotic expansion, Gaussian radial isometry, or
spectral eigenvalue enumeration is presumed.
-/

noncomputable section
namespace GegenbauerFock.KummerCoefficients

/-- The actual unregularized Kummer mass contains its vacuum term
and an explicitly nonnegative first excited contribution. -/
theorem kummerSeries_ge_vacuum_add_first
    (lam z : ℝ) (hlam : 0 < lam) (hz : 0 ≤ z) :
    1 + ratio lam 1 * z ≤ kummerSeries lam z := by
  have hs := kummerSeries_summable lam z hlam hz
  have hnn (n : ℕ) :
      0 ≤ ratio lam n * (z ^ n / (Nat.factorial n : ℝ)) :=
    mul_nonneg (ratio_nonneg lam hlam n) (by positivity)
  have hprefix :
      (∑ n ∈ Finset.range 2,
        ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) ≤
        kummerSeries lam z := by
    exact hs.sum_le_tsum (Finset.range 2) (fun n _ => hnn n)
  have hfirst :
      (∑ n ∈ Finset.range 2,
        ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) =
        1 + ratio lam 1 * z := by
    simp [Finset.sum_range_succ, ratio_zero]
  rw [hfirst] at hprefix
  exact hprefix

/-- For strictly positive Kummer argument, the n=1 term makes
the trace mass strictly larger than the vacuum contribution. -/
theorem kummerSeries_gt_one
    (lam z : ℝ) (hlam : 0 < lam) (hz : 0 < z) :
    1 < kummerSeries lam z := by
  have hratio : 0 < ratio lam 1 := by
    have hdenom : 0 < lam + 1 := by linarith
    have hquot : 0 < (1 / 2 : ℝ) / (lam + 1) :=
      div_pos (by norm_num) hdenom
    simpa [ratio] using hquot
  have hfirst : 1 < 1 + ratio lam 1 * z := by
    nlinarith [mul_pos hratio hz]
  exact lt_of_lt_of_le hfirst
    (kummerSeries_ge_vacuum_add_first lam z hlam hz.le)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_ge_vacuum_add_first
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_gt_one

end GegenbauerFock.KummerCoefficients
