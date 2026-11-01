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


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Stable Gaussian-width recovery from errors in actual basis-invariant
analytic Fock Hilbert–Schmidt squared energy observations. -/
theorem C_intrinsicEntire_HS_energy_alpha_noisy_recovery
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (h₁ : |(∑' i : ι₁,
        ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |(∑' i : ι₂,
        ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤ 8 * (lam + 1) * A ^ 2 * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₁ hlam ha₁ b₁] at h₁
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₂ hlam ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_alpha_noisy_recovery
    lam alpha₁ alpha₂ A y eps₁ eps₂ hlam ha₁ ha₂ hA₁ hA₂ h₁ h₂

/-- Identical bounded-error recovery bound from the real diagonal
source-Gram trace for two arbitrary complete source Hilbert bases. -/
theorem C_intrinsicEntire_Gram_trace_alpha_noisy_recovery
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (h₁ : |(∑' i : ι₁, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b₁ i)) (b₁ i))) - y|
        ≤ eps₁)
    (h₂ : |(∑' i : ι₂, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b₂ i)) (b₂ i))) - y|
        ≤ eps₂) :
    |alpha₁ - alpha₂| ≤ 8 * (lam + 1) * A ^ 2 * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₁ hlam ha₁ b₁] at h₁
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₂ hlam ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_alpha_noisy_recovery
    lam alpha₁ alpha₂ A y eps₁ eps₂ hlam ha₁ ha₂ hA₁ hA₂ h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_alpha_noisy_recovery
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_alpha_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
