import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaInverseStability
import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer

/-!
# V007 — inverse Lipschitz stability measured in the genuine S₂ norm

The previous inverse Lipschitz estimate uses squared S₂ masses. This
module converts it into an explicit stability inequality for the
nonnegative basis-defined Hilbert–Schmidt norm itself.

The conversion is quantitative, using the square-root factorization
of two nonnegative Kummer masses and the previously certified universal
exponential majorant. The two source Hilbert bases may be unrelated.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The exact scalar Kummer mass difference is bounded by twice the
square root of its exponential upper bound, times the difference of
the two nonnegative square roots. -/
theorem kummerSeries_sqrt_difference_bound
    (lam₁ lam₂ z : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hz : 0 ≤ z) :
    |kummerSeries lam₁ z - kummerSeries lam₂ z| ≤
      2 * Real.sqrt (Real.exp z) *
        |Real.sqrt (kummerSeries lam₁ z) -
         Real.sqrt (kummerSeries lam₂ z)| := by
  have h1 : 0 ≤ kummerSeries lam₁ z := by
    have h := kummerSeries_ge_one lam₁ z hlam₁ hz
    linarith
  have h2 : 0 ≤ kummerSeries lam₂ z := by
    have h := kummerSeries_ge_one lam₂ z hlam₂ hz
    linarith
  have hsq1 := Real.sq_sqrt h1
  have hsq2 := Real.sq_sqrt h2
  have hfactor :
      kummerSeries lam₁ z - kummerSeries lam₂ z =
        (Real.sqrt (kummerSeries lam₁ z) -
         Real.sqrt (kummerSeries lam₂ z)) *
        (Real.sqrt (kummerSeries lam₁ z) +
         Real.sqrt (kummerSeries lam₂ z)) := by
    nlinarith
  have hsqrt1 :
      Real.sqrt (kummerSeries lam₁ z) ≤ Real.sqrt (Real.exp z) :=
    Real.sqrt_le_sqrt (kummerSeries_le_exp lam₁ z hlam₁ hz)
  have hsqrt2 :
      Real.sqrt (kummerSeries lam₂ z) ≤ Real.sqrt (Real.exp z) :=
    Real.sqrt_le_sqrt (kummerSeries_le_exp lam₂ z hlam₂ hz)
  have hsumbound :
      Real.sqrt (kummerSeries lam₁ z) +
        Real.sqrt (kummerSeries lam₂ z) ≤
          2 * Real.sqrt (Real.exp z) := by linarith
  calc
    |kummerSeries lam₁ z - kummerSeries lam₂ z| =
        |Real.sqrt (kummerSeries lam₁ z) -
         Real.sqrt (kummerSeries lam₂ z)| *
          (Real.sqrt (kummerSeries lam₁ z) +
           Real.sqrt (kummerSeries lam₂ z)) := by
      rw [hfactor, abs_mul,
        abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    _ ≤ |Real.sqrt (kummerSeries lam₁ z) -
          Real.sqrt (kummerSeries lam₂ z)| *
          (2 * Real.sqrt (Real.exp z)) :=
      mul_le_mul_of_nonneg_left hsumbound (abs_nonneg _)
    _ = 2 * Real.sqrt (Real.exp z) *
          |Real.sqrt (kummerSeries lam₁ z) -
           Real.sqrt (kummerSeries lam₂ z)| := by ring

/-- On 0 < λ ≤ L, the square root of the true Kummer mass determines
λ with an explicit inverse Lipschitz modulus at fixed α > 0. -/
theorem kummerSeries_sqrt_lambda_inverse_stability
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha) :
    |lam₁ - lam₂| ≤
      16 * alpha * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * alpha))) *
        |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) -
         Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))| := by
  have hconstant : 0 ≤ 8 * alpha * (L + 1) ^ 2 := by positivity
  have hbound := kummerSeries_sqrt_difference_bound
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hlam₂ (by positivity)
  calc
    |lam₁ - lam₂| ≤
        8 * alpha * (L + 1) ^ 2 *
          |kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))| :=
      kummerSeries_lambda_inverse_stability
        lam₁ lam₂ L alpha hlam₁ hlam₂ hL₁ hL₂ ha
    _ ≤ 8 * alpha * (L + 1) ^ 2 *
          (2 * Real.sqrt (Real.exp (1 / (4 * alpha))) *
           |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) -
            Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))|) :=
      mul_le_mul_of_nonneg_left hbound hconstant
    _ = 16 * alpha * (L + 1) ^ 2 *
          Real.sqrt (Real.exp (1 / (4 * alpha))) *
          |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha))) -
           Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha)))| := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_sqrt_difference_bound
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_sqrt_lambda_inverse_stability

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Inverse Lipschitz stability for the true, unsquared source-basis
Gaussian analytic-Fock Hilbert–Schmidt norm. -/
theorem C_intrinsicEntire_basisHSNorm_lambda_inverse_stability
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    |lam₁ - lam₂| ≤
      16 * alpha * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * alpha))) *
        |Real.sqrt (∑' i : ι₁,
          ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) -
         Real.sqrt (∑' i : ι₂,
          ‖C_intrinsicEntire lam₂ alpha hlam₂ ha (b₂ i)‖ ^ 2)| := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam₁ alpha hlam₁ ha b₁,
    C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam₂ alpha hlam₂ ha b₂]
  exact KummerCoefficients.kummerSeries_sqrt_lambda_inverse_stability
    lam₁ lam₂ L alpha hlam₁ hlam₂ hL₁ hL₂ ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_lambda_inverse_stability

end GegenbauerFock.GeneralUltrasphericalFock
