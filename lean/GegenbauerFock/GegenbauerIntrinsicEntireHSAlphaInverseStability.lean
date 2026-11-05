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


namespace GegenbauerFock.KummerCoefficients

/-- Global inverse Lipschitz estimate on positive Gaussian widths
alpha₁, alpha₂ ≤ A for fixed positive ultraspherical lambda. -/
theorem kummerSeries_alpha_inverse_stability
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        |kummerSeries lam (1 / (4 * alpha₁)) -
         kummerSeries lam (1 / (4 * alpha₂))| := by
  rcases le_total alpha₁ alpha₂ with hle | hle
  · have hb := kummerSeries_alpha_inverse_stability_ordered
      lam alpha₁ alpha₂ A hlam ha₁ ha₂ hle hA₁ hA₂
    have hg := kummerSeries_alpha_first_gap
      lam alpha₁ alpha₂ hlam ha₁ ha₂ hle
    have hden : 0 ≤ 8 * (lam + 1) * alpha₁ * alpha₂ := by positivity
    have hnonneg :
        0 ≤ kummerSeries lam (1 / (4 * alpha₁)) -
            kummerSeries lam (1 / (4 * alpha₂)) :=
      (div_nonneg (sub_nonneg.mpr hle) hden).trans hg
    calc
      |alpha₁ - alpha₂| = alpha₂ - alpha₁ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      _ ≤ 8 * (lam + 1) * A ^ 2 *
           (kummerSeries lam (1 / (4 * alpha₁)) -
            kummerSeries lam (1 / (4 * alpha₂))) := hb
      _ = 8 * (lam + 1) * A ^ 2 *
           |kummerSeries lam (1 / (4 * alpha₁)) -
            kummerSeries lam (1 / (4 * alpha₂))| := by
        rw [abs_of_nonneg hnonneg]
  · have hb := kummerSeries_alpha_inverse_stability_ordered
      lam alpha₂ alpha₁ A hlam ha₂ ha₁ hle hA₂ hA₁
    have hg := kummerSeries_alpha_first_gap
      lam alpha₂ alpha₁ hlam ha₂ ha₁ hle
    have hden : 0 ≤ 8 * (lam + 1) * alpha₂ * alpha₁ := by positivity
    have hnonneg :
        0 ≤ kummerSeries lam (1 / (4 * alpha₂)) -
            kummerSeries lam (1 / (4 * alpha₁)) :=
      (div_nonneg (sub_nonneg.mpr hle) hden).trans hg
    calc
      |alpha₁ - alpha₂| = alpha₁ - alpha₂ :=
        abs_of_nonneg (sub_nonneg.mpr hle)
      _ ≤ 8 * (lam + 1) * A ^ 2 *
           (kummerSeries lam (1 / (4 * alpha₂)) -
            kummerSeries lam (1 / (4 * alpha₁))) := hb
      _ = 8 * (lam + 1) * A ^ 2 *
           |kummerSeries lam (1 / (4 * alpha₁)) -
            kummerSeries lam (1 / (4 * alpha₂))| := by
        rw [abs_of_nonpos (sub_nonpos.mpr (by linarith : kummerSeries lam (1 / (4 * alpha₁)) ≤ kummerSeries lam (1 / (4 * alpha₂))))]
        ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_inverse_stability

end GegenbauerFock.KummerCoefficients


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Global α inverse Lipschitz bound from the actual entire-Fock
basis-independent Hilbert–Schmidt squared energies. -/
theorem C_intrinsicEntire_HS_energy_alpha_inverse_stability
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    |alpha₁ - alpha₂| ≤ 8 * (lam + 1) * A ^ 2 *
      |(∑' i : ι₁, ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) -
       (∑' i : ι₂, ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2)| := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₁ hlam ha₁ b₁,
      C_intrinsicEntire_HS_energy_eq_kummer lam alpha₂ hlam ha₂ b₂]
  exact KummerCoefficients.kummerSeries_alpha_inverse_stability
    lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂

/-- The same quantitative α inverse estimate from genuine
source-Gram real diagonal traces. -/
theorem C_intrinsicEntire_Gram_trace_alpha_inverse_stability
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    |alpha₁ - alpha₂| ≤ 8 * (lam + 1) * A ^ 2 *
      |(∑' i : ι₁, RCLike.re (inner ℂ
         (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b₁ i)) (b₁ i))) -
       (∑' i : ι₂, RCLike.re (inner ℂ
         (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b₂ i)) (b₂ i)))| := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₁ hlam ha₁ b₁,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₂ hlam ha₂ b₂]
  exact KummerCoefficients.kummerSeries_alpha_inverse_stability
    lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_alpha_inverse_stability
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_alpha_inverse_stability

end GegenbauerFock.GeneralUltrasphericalFock
