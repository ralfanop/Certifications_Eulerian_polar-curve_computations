import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaNormUniformStability

/-!
# V007 — uniform noise-stable Gaussian-width reconstruction

On the compact interval [a,A], where 0 < a ≤ A, the actual Gaussian-Fock
Hilbert–Schmidt norm N(lambda,alpha) = sqrt(H(lambda,alpha)) admits
a uniform inverse Lipschitz bound. Consequently any two candidate
Gaussian widths fitting one observed S2 norm y with absolute
measurement errors eps₁, eps₂ satisfy an explicit uniform estimate.

Unlike data-dependent estimates, the constant uses only the known
prior bounds a,A,lambda.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Error-stable scalar recovery with a uniform inverse modulus
on a compact positive Gaussian-width interval. -/
theorem kummerSeries_alpha_sqrt_uniform_noisy_recovery
    (lam alpha₁ alpha₂ a A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha : 0 < a)
    (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hhi₁ : alpha₁ ≤ A) (hhi₂ : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by
  have ht :
      |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| ≤
        eps₁ + eps₂ := by
    calc
      |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| ≤
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| +
        |y - Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| :=
          abs_sub_le _ _ _
      _ = |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) - y| +
          |Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) - y| := by
        rw [abs_sub_comm y (Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hc : 0 ≤
      16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) := by positivity
  exact (kummerSeries_alpha_sqrt_uniform_inverse_stability
    lam alpha₁ alpha₂ a A hlam ha hlo₁ hlo₂ hhi₁ hhi₂).trans
      (mul_le_mul_of_nonneg_left ht hc)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_sqrt_uniform_noisy_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Uniform error-stable recovery of Gaussian alpha from measurements
of the genuine intrinsic entire-Fock Hilbert–Schmidt norm, with
independent complete source Hilbert bases. -/
theorem C_intrinsicEntire_basisHSNorm_alpha_uniform_noisy_recovery
    (lam alpha₁ alpha₂ a A y eps₁ eps₂ : ℝ)
    (hlam : 0 < lam) (ha : 0 < a)
    (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hhi₁ : alpha₁ ≤ A) (hhi₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam alpha₁ hlam (lt_of_lt_of_le ha hlo₁) (b₁ i)‖ ^ 2) -
        y| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam alpha₂ hlam (lt_of_lt_of_le ha hlo₂) (b₂ i)‖ ^ 2) -
        y| ≤ eps₂) :
    |alpha₁ - alpha₂| ≤
      16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₁ hlam (lt_of_lt_of_le ha hlo₁) b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₂ hlam (lt_of_lt_of_le ha hlo₂) b₂] at h₂
  exact KummerCoefficients.kummerSeries_alpha_sqrt_uniform_noisy_recovery
    lam alpha₁ alpha₂ a A y eps₁ eps₂ hlam ha hlo₁ hlo₂ hhi₁ hhi₂ h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_alpha_uniform_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
