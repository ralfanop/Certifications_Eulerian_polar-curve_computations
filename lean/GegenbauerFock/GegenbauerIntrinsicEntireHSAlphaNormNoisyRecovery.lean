import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaNormStability

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Error propagation for recovering alpha from noisy unsquared
Kummer/Fock Hilbert–Schmidt mass. The stability factor is adaptive. -/
theorem kummerSeries_alpha_sqrt_noisy_recovery
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
        (eps₁ + eps₂) := by
  have ht :
      |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| ≤ eps₁ + eps₂ := by
    calc
      |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| ≤
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| +
        |y - Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| :=
          abs_sub_le _ _ _
      _ = |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| +
          |Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y| := by
        rw [abs_sub_comm y
          (Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hc :
      0 ≤ 8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) := by positivity
  exact (kummerSeries_alpha_sqrt_inverse_stability
    lam alpha₁ alpha₂ A hlam ha₁ ha₂ hA₁ hA₂).trans
      (mul_le_mul_of_nonneg_left ht hc)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_sqrt_noisy_recovery

end GegenbauerFock.KummerCoefficients


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Error-stable recovery of the Gaussian width from actual unsquared
intrinsic Fock Hilbert–Schmidt norms, allowing different complete bases. -/
theorem C_intrinsicEntire_basisHSNorm_alpha_noisy_recovery
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (∑' i : ι₁,
          ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) +
         Real.sqrt (∑' i : ι₂,
          ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2)) *
        (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₁ hlam ha₁ b₁] at h₁ ⊢
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₂ hlam ha₂ b₂] at h₂ ⊢
  exact KummerCoefficients.kummerSeries_alpha_sqrt_noisy_recovery
    lam alpha₁ alpha₂ A y eps₁ eps₂ hlam ha₁ ha₂ hA₁ hA₂ h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_alpha_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
