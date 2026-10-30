import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaFirstGap

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Quantitative recovery of Gaussian width alpha on (0,A],
ordered by alpha₁ ≤ alpha₂, from exact Kummer masses. -/
theorem kummerSeries_alpha_inverse_stability_ordered
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hle : alpha₁ ≤ alpha₂) (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A) :
    alpha₂ - alpha₁ ≤
      8 * (lam + 1) * A ^ 2 *
        (kummerSeries lam (1 / (4 * alpha₁)) -
         kummerSeries lam (1 / (4 * alpha₂))) := by
  have hgap := kummerSeries_alpha_first_gap
    lam alpha₁ alpha₂ hlam ha₁ ha₂ hle
  have hden : 0 < 8 * (lam + 1) * alpha₁ * alpha₂ := by positivity
  have hdiff :
      0 ≤ kummerSeries lam (1 / (4 * alpha₁)) -
        kummerSeries lam (1 / (4 * alpha₂)) :=
    (div_nonneg (sub_nonneg.mpr hle) hden.le).trans hgap
  have hApos : 0 ≤ A := le_trans ha₁.le hA₁
  have hprod : alpha₁ * alpha₂ ≤ A ^ 2 := by
    calc
      alpha₁ * alpha₂ ≤ A * alpha₂ :=
        mul_le_mul_of_nonneg_right hA₁ ha₂.le
      _ ≤ A * A := mul_le_mul_of_nonneg_left hA₂ hApos
      _ = A ^ 2 := by ring
  have hdenbound :
      8 * (lam + 1) * alpha₁ * alpha₂ ≤ 8 * (lam + 1) * A ^ 2 := by
    calc
      8 * (lam + 1) * alpha₁ * alpha₂ =
          (8 * (lam + 1)) * (alpha₁ * alpha₂) := by ring
      _ ≤ (8 * (lam + 1)) * A ^ 2 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
  calc
    alpha₂ - alpha₁ ≤
      (kummerSeries lam (1 / (4 * alpha₁)) -
       kummerSeries lam (1 / (4 * alpha₂))) *
        (8 * (lam + 1) * alpha₁ * alpha₂) :=
      (div_le_iff₀ hden).mp hgap
    _ ≤ (kummerSeries lam (1 / (4 * alpha₁)) -
          kummerSeries lam (1 / (4 * alpha₂))) *
          (8 * (lam + 1) * A ^ 2) :=
      mul_le_mul_of_nonneg_left hdenbound hdiff
    _ = 8 * (lam + 1) * A ^ 2 *
          (kummerSeries lam (1 / (4 * alpha₁)) -
           kummerSeries lam (1 / (4 * alpha₂))) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_inverse_stability_ordered

end GegenbauerFock.KummerCoefficients
