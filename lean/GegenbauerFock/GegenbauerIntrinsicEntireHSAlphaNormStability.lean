import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaInverseStability

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Exact, data-dependent inverse stability of Gaussian width alpha,
expressed in terms of the genuine (unsquared) Kummer S2 mass. -/
theorem kummerSeries_alpha_sqrt_inverse_stability
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| := by
  have h₁ : 0 ≤ kummerSeries lam (1 / (4 * alpha₁)) := by
    have h := kummerSeries_ge_one lam (1 / (4 * alpha₁))
      hlam (by positivity)
    linarith
  have h₂ : 0 ≤ kummerSeries lam (1 / (4 * alpha₂)) := by
    have h := kummerSeries_ge_one lam (1 / (4 * alpha₂))
      hlam (by positivity)
    linarith
  have hfactor :
      kummerSeries lam (1 / (4 * alpha₁)) -
        kummerSeries lam (1 / (4 * alpha₂)) =
      (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
      (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) := by
    nlinarith [Real.sq_sqrt h₁, Real.sq_sqrt h₂]
  have habs :
      |kummerSeries lam (1 / (4 * alpha₁)) -
        kummerSeries lam (1 / (4 * alpha₂))| =
      |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| *
      (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) := by
    rw [hfactor, abs_mul,
        abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  calc
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        |kummerSeries lam (1 / (4 * alpha₁)) -
         kummerSeries lam (1 / (4 * alpha₂))| :=
      kummerSeries_alpha_inverse_stability
        lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂
    _ = 8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| := by
      rw [habs]
      ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_sqrt_inverse_stability

end GegenbauerFock.KummerCoefficients
