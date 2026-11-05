import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaNormStability

/-!
# V007 — uniform Gaussian-width inverse stability from the actual S₂ norm

For a ≤ alpha₁,alpha₂ ≤ A with a > 0 and fixed lambda > 0, the
adaptive S₂-norm inverse estimate becomes a uniform Lipschitz estimate,
using H(lambda,alpha) ≤ exp(1/(4*a)).

This distinguishes a finite-dimensional scalar parameter inversion
from the ill-posed infinite-dimensional inverse Fock operator.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- A uniform inverse Lipschitz bound on any compact interval [a,A]
of positive Gaussian widths for the square root of the Kummer mass. -/
theorem kummerSeries_alpha_sqrt_uniform_inverse_stability
    (lam alpha₁ alpha₂ a A : ℝ)
    (hlam : 0 < lam) (ha : 0 < a)
    (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hhi₁ : alpha₁ ≤ A) (hhi₂ : alpha₂ ≤ A) :
    |alpha₁ - alpha₂| ≤
      16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| := by
  have ha₁ : 0 < alpha₁ := lt_of_lt_of_le ha hlo₁
  have ha₂ : 0 < alpha₂ := lt_of_lt_of_le ha hlo₂
  have harg₁ : (1 / (4 * alpha₁) : ℝ) ≤ 1 / (4 * a) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have harg₂ : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * a) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hK₁ :
      kummerSeries lam (1 / (4 * alpha₁)) ≤ Real.exp (1 / (4 * a)) :=
    (kummerSeries_le_exp lam (1 / (4 * alpha₁)) hlam (by positivity)).trans
      (Real.exp_le_exp.mpr harg₁)
  have hK₂ :
      kummerSeries lam (1 / (4 * alpha₂)) ≤ Real.exp (1 / (4 * a)) :=
    (kummerSeries_le_exp lam (1 / (4 * alpha₂)) hlam (by positivity)).trans
      (Real.exp_le_exp.mpr harg₂)
  have hs₁ := Real.sqrt_le_sqrt hK₁
  have hs₂ := Real.sqrt_le_sqrt hK₂
  have hsum :
      Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) ≤
        2 * Real.sqrt (Real.exp (1 / (4 * a))) := by linarith
  have hterm :
      (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
       |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| ≤
      (2 * Real.sqrt (Real.exp (1 / (4 * a)))) *
       |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| :=
    mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
  calc
    |alpha₁ - alpha₂| ≤
      8 * (lam + 1) * A ^ 2 *
        (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| :=
      kummerSeries_alpha_sqrt_inverse_stability
        lam alpha₁ alpha₂ A hlam ha₁ ha₂ hhi₁ hhi₂
    _ ≤ 8 * (lam + 1) * A ^ 2 *
        ((2 * Real.sqrt (Real.exp (1 / (4 * a)))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))|) := by
      calc
        8 * (lam + 1) * A ^ 2 *
          (Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
           Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
          |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
           Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| =
          8 * (lam + 1) * A ^ 2 *
          ((Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) +
            Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))) *
            |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
             Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))|) := by ring
        _ ≤ 8 * (lam + 1) * A ^ 2 *
          ((2 * Real.sqrt (Real.exp (1 / (4 * a)))) *
            |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
             Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))|) :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = 16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) *
        |Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) -
         Real.sqrt (kummerSeries lam (1 / (4 * alpha₂)))| := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_sqrt_uniform_inverse_stability

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Basis-independent uniform inverse stability in alpha, using only
the actual S₂ norm of the intrinsic entire-Fock transform. -/
theorem C_intrinsicEntire_basisHSNorm_alpha_uniform_inverse_stability
    (lam alpha₁ alpha₂ a A : ℝ)
    (hlam : 0 < lam) (ha : 0 < a)
    (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hhi₁ : alpha₁ ≤ A) (hhi₂ : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    |alpha₁ - alpha₂| ≤
      16 * (lam + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) *
        |Real.sqrt (∑' i : ι₁,
          ‖C_intrinsicEntire lam alpha₁ hlam (lt_of_lt_of_le ha hlo₁) (b₁ i)‖ ^ 2) -
         Real.sqrt (∑' i : ι₂,
          ‖C_intrinsicEntire lam alpha₂ hlam (lt_of_lt_of_le ha hlo₂) (b₂ i)‖ ^ 2)| := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₁ hlam (lt_of_lt_of_le ha hlo₁) b₁,
      C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
      lam alpha₂ hlam (lt_of_lt_of_le ha hlo₂) b₂]
  exact KummerCoefficients.kummerSeries_alpha_sqrt_uniform_inverse_stability
    lam alpha₁ alpha₂ a A hlam ha hlo₁ hlo₂ hhi₁ hhi₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_alpha_uniform_inverse_stability

end GegenbauerFock.GeneralUltrasphericalFock
