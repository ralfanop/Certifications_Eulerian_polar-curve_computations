import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaNormNoisyRecovery

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- An entirely observation-based Gaussian-width recovery guarantee:
the multiplicative stability factor involves only the measured
Hilbert–Schmidt norm and the two certified error budgets. -/
theorem kummerSeries_alpha_observed_error_stability
    (lam alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hA₁ : alpha₁ ≤ A) (hA₂ : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
  have he₁ : 0 ≤ eps₁ := (abs_nonneg _).trans h₁
  have he₂ : 0 ≤ eps₂ := (abs_nonneg _).trans h₂
  have herrors : 0 ≤ eps₁ + eps₂ := add_nonneg he₁ he₂
  have hu₁ : Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y ≤ eps₁ :=
    (abs_le.mp h₁).2
  have hu₂ : Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y ≤ eps₂ :=
    (abs_le.mp h₂).2
  have hy : y ≤ |y| := le_abs_self y
  have hsum :
      Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
      Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) ≤
      2 * |y| + eps₁ + eps₂ := by linarith
  have hc : 0 ≤ 8 * (lam + 1) * A ^ 2 := by positivity
  calc
    |alpha₁ - alpha₂| ≤
        8 * (lam + 1) * A ^ 2 *
          (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
           Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
          (eps₁ + eps₂) :=
      kummerSeries_alpha_sqrt_noisy_recovery
        lam alpha₁ alpha₂ A y eps₁ eps₂
        hlam ha₁ ha₂ hA₁ hA₂ h₁ h₂
    _ ≤ 8 * (lam + 1) * A ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
      calc
        8 * (lam + 1) * A ^ 2 *
          (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
           Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
          (eps₁ + eps₂) =
          8 * (lam + 1) * A ^ 2 *
          ((Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
            Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
            (eps₁ + eps₂)) := by ring
        _ ≤ 8 * (lam + 1) * A ^ 2 *
          ((2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsum herrors) hc
        _ = 8 * (lam + 1) * A ^ 2 *
          (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_observed_error_stability

end GegenbauerFock.KummerCoefficients


open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Parameter recovery bound depending only on the observed true Fock
S2 norm and error budgets, rather than unknown exact S2 norms. -/
theorem C_intrinsicEntire_basisHSNorm_alpha_observed_error_stability
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
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₁ hlam ha₁ b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₂ hlam ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_alpha_observed_error_stability
    lam alpha₁ alpha₂ A y eps₁ eps₂
    hlam ha₁ ha₂ hA₁ hA₂ h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_alpha_observed_error_stability

end GegenbauerFock.GeneralUltrasphericalFock
