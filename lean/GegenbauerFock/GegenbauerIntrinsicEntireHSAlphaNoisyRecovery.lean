import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaInverseStability

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Recovery of positive Gaussian width alpha on (0,A] from the
true scalar Kummer mass observed with bounded absolute error. -/
theorem kummerSeries_alpha_noisy_recovery
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    (h₁ : |kummerSeries lam (1 / (4 * alpha₁)) - y| ≤ eps₁)
    (h₂ : |kummerSeries lam (1 / (4 * alpha₂)) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 * (eps₁ + eps₂) := by
  have ht :
      |kummerSeries lam (1 / (4 * alpha₁)) -
       kummerSeries lam (1 / (4 * alpha₂))| ≤ eps₁ + eps₂ := by
    calc
      |kummerSeries lam (1 / (4 * alpha₁)) -
       kummerSeries lam (1 / (4 * alpha₂))| ≤
        |kummerSeries lam (1 / (4 * alpha₁)) - y| +
        |y - kummerSeries lam (1 / (4 * alpha₂))| :=
          abs_sub_le _ _ _
      _ = |kummerSeries lam (1 / (4 * alpha₁)) - y| +
          |kummerSeries lam (1 / (4 * alpha₂)) - y| := by
        rw [abs_sub_comm y (kummerSeries lam (1 / (4 * alpha₂)))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hc : 0 ≤ 8 * (lam + 1) * A ^ 2 := by positivity
  exact (kummerSeries_alpha_inverse_stability
    lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂).trans
      (mul_le_mul_of_nonneg_left ht hc)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_noisy_recovery

end GegenbauerFock.KummerCoefficients
