import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaInverseStability

/-!
# V007 — error-stable recovery of the ultraspherical lambda parameter

Two positive lambda parameters in a bounded interval are close whenever
their real Kummer masses are close to the same observed scalar, with
a fully explicit error-propagation constant.

The theorem transfers unchanged to the genuine analytic Gaussian-Fock
source-basis Hilbert–Schmidt energies and source-Gram diagonal traces,
allowing unrelated source Hilbert spaces and complete bases.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Two candidate parameters whose exact Kummer masses fit a single
observation within errors epsilon₁ and epsilon₂ are separated by at
most 8 alpha (L+1)^2 (epsilon₁ + epsilon₂). -/
theorem kummerSeries_lambda_noisy_recovery
    (lam₁ lam₂ L alpha observation epsilon₁ epsilon₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    (hobs₁ :
      |kummerSeries lam₁ (1 / (4 * alpha)) - observation| ≤ epsilon₁)
    (hobs₂ :
      |kummerSeries lam₂ (1 / (4 * alpha)) - observation| ≤ epsilon₂) :
    |lam₁ - lam₂| ≤
      8 * alpha * (L + 1) ^ 2 * (epsilon₁ + epsilon₂) := by
  have htriangle :
      |kummerSeries lam₁ (1 / (4 * alpha)) -
          kummerSeries lam₂ (1 / (4 * alpha))| ≤
      |kummerSeries lam₁ (1 / (4 * alpha)) - observation| +
        |kummerSeries lam₂ (1 / (4 * alpha)) - observation| := by
    calc
      |kummerSeries lam₁ (1 / (4 * alpha)) -
          kummerSeries lam₂ (1 / (4 * alpha))| ≤
          |kummerSeries lam₁ (1 / (4 * alpha)) - observation| +
          |observation - kummerSeries lam₂ (1 / (4 * alpha))| :=
        abs_sub_le _ _ _
      _ = |kummerSeries lam₁ (1 / (4 * alpha)) - observation| +
          |kummerSeries lam₂ (1 / (4 * alpha)) - observation| := by
        rw [abs_sub_comm observation
          (kummerSeries lam₂ (1 / (4 * alpha)))]
  have hconstant : 0 ≤ 8 * alpha * (L + 1) ^ 2 := by positivity
  calc
    |lam₁ - lam₂| ≤
        8 * alpha * (L + 1) ^ 2 *
          |kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))| :=
      kummerSeries_lambda_inverse_stability
        lam₁ lam₂ L alpha hlam₁ hlam₂ hL₁ hL₂ ha
    _ ≤ 8 * alpha * (L + 1) ^ 2 *
        (|kummerSeries lam₁ (1 / (4 * alpha)) - observation| +
         |kummerSeries lam₂ (1 / (4 * alpha)) - observation|) :=
      mul_le_mul_of_nonneg_left htriangle hconstant
    _ ≤ 8 * alpha * (L + 1) ^ 2 * (epsilon₁ + epsilon₂) :=
      mul_le_mul_of_nonneg_left (add_le_add hobs₁ hobs₂) hconstant

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_lambda_noisy_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Error-stable scalar recovery of lambda from genuine entire Gaussian-Fock
Hilbert–Schmidt source energies for arbitrary complete source bases. -/
theorem C_intrinsicEntire_HS_energy_lambda_noisy_recovery
    (lam₁ lam₂ L alpha observation epsilon₁ epsilon₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (hobs₁ :
      |(∑' i : ι₁,
         ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) -
          observation| ≤ epsilon₁)
    (hobs₂ :
      |(∑' i : ι₂,
         ‖C_intrinsicEntire lam₂ alpha hlam₂ ha (b₂ i)‖ ^ 2) -
          observation| ≤ epsilon₂) :
    |lam₁ - lam₂| ≤
      8 * alpha * (L + 1) ^ 2 * (epsilon₁ + epsilon₂) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha hlam₁ ha b₁] at hobs₁
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₂ alpha hlam₂ ha b₂] at hobs₂
  exact KummerCoefficients.kummerSeries_lambda_noisy_recovery
    lam₁ lam₂ L alpha observation epsilon₁ epsilon₂
    hlam₁ hlam₂ hL₁ hL₂ ha hobs₁ hobs₂

/-- Equivalent error stability for genuine analytic Gaussian-Fock
intrinsic source-Gram real diagonal traces. -/
theorem C_intrinsicEntire_Gram_trace_lambda_noisy_recovery
    (lam₁ lam₂ L alpha observation epsilon₁ epsilon₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (hobs₁ :
      |(∑' i : ι₁, RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) -
        observation| ≤ epsilon₁)
    (hobs₂ :
      |(∑' i : ι₂, RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam₂ alpha hlam₂ ha (b₂ i)) (b₂ i))) -
        observation| ≤ epsilon₂) :
    |lam₁ - lam₂| ≤
      8 * alpha * (L + 1) ^ 2 * (epsilon₁ + epsilon₂) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₁ alpha hlam₁ ha b₁] at hobs₁
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₂ alpha hlam₂ ha b₂] at hobs₂
  exact KummerCoefficients.kummerSeries_lambda_noisy_recovery
    lam₁ lam₂ L alpha observation epsilon₁ epsilon₂
    hlam₁ hlam₂ hL₁ hL₂ ha hobs₁ hobs₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_lambda_noisy_recovery
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_lambda_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
