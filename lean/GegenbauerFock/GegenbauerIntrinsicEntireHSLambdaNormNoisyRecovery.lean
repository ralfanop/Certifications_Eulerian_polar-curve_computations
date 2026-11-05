import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaNormStability

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Two positive source parameters with approximately equal measured
Hilbert–Schmidt norms are quantitatively close. -/
theorem kummerSeries_sqrt_lambda_noisy_recovery
    (lam₁ lam₂ L alpha y eps₁ eps₂ : ℝ)
    (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha))) - y| ≤ eps₂) :
    |lam₁ - lam₂| ≤
      16 * alpha * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * alpha))) * (eps₁ + eps₂) := by
  have ht :
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))| ≤
        eps₁ + eps₂ := by
    calc
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))| ≤
        |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) - y| +
        |y - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))| :=
          abs_sub_le _ _ _
      _ = |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) - y| +
          |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha))) - y| := by
        rw [abs_sub_comm y (Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha))))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hc : 0 ≤
      16 * alpha * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * alpha))) := by positivity
  exact (kummerSeries_sqrt_lambda_inverse_stability
    lam₁ lam₂ L alpha hl₁ hl₂ hL₁ hL₂ ha).trans
      (mul_le_mul_of_nonneg_left ht hc)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_sqrt_lambda_noisy_recovery

end GegenbauerFock.KummerCoefficients


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Robust identification of λ by the actual basis-defined Gaussian-Fock
Hilbert–Schmidt norm, allowing unrelated complete Hilbert bases. -/
theorem C_intrinsicEntire_basisHSNorm_lambda_noisy_recovery
    (lam₁ lam₂ L alpha y eps₁ eps₂ : ℝ)
    (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha hl₁ ha (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha hl₂ ha (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    |lam₁ - lam₂| ≤ 16 * alpha * (L + 1) ^ 2 *
      Real.sqrt (Real.exp (1 / (4 * alpha))) * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₁ alpha hl₁ ha b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₂ alpha hl₂ ha b₂] at h₂
  exact KummerCoefficients.kummerSeries_sqrt_lambda_noisy_recovery
    lam₁ lam₂ L alpha y eps₁ eps₂ hl₁ hl₂ hL₁ hL₂ ha h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_lambda_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
