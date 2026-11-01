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


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Adaptive inverse stability in Gaussian alpha of the actual
basis-defined intrinsic analytic-Fock unsquared Hilbert–Schmidt norm. -/
theorem C_intrinsicEntire_basisHSNorm_alpha_inverse_stability
    (lam alpha₁ alpha₂ A : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (∑' i : ι₁,
          ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) +
         Real.sqrt (∑' i : ι₂,
          ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2)) *
        |Real.sqrt (∑' i : ι₁,
          ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) -
         Real.sqrt (∑' i : ι₂,
          ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2)| := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam alpha₁ hlam ha₁ b₁,
      C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam alpha₂ hlam ha₂ b₂]
  exact KummerCoefficients.kummerSeries_alpha_sqrt_inverse_stability
    lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_alpha_inverse_stability

end GegenbauerFock.GeneralUltrasphericalFock
