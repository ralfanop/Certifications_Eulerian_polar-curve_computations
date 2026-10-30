import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaQuantitative
import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaFirstGap

/-!
# V007 — simultaneous quantitative lambda and Gaussian-width separation

For positive ordered parameters lambda₁ ≤ lambda₂ and
alpha₁ ≤ alpha₂, the difference of the genuine Kummer/Gaussian Fock
Hilbert–Schmidt energies is bounded below by the sum of two *exact*
first-excited-coefficient contributions.

The two terms separately measure the lambda and alpha parameter gaps.
The result transfers to S₂ energies and intrinsic Gram traces on
unrelated complete source Hilbert bases. It is a statement for
coordinatewise comparable parameter pairs only.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Mixed quantitative strict separation from the first excited
Kummer coefficient in each increasing coordinate. -/
theorem kummerSeries_mixed_quantitative_gap
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
      kummerSeries lam₂ (1 / (4 * alpha₂)) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have hλ :
      (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) ≤
        kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₁)) := by
    calc
      (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) =
          (ratio lam₁ 1 - ratio lam₂ 1) * (1 / (4 * alpha₁)) :=
        (ratio_lambda_first_gap_gaussian_exact
          lam₁ lam₂ alpha₁ hlam₁ hlam₂ ha₁).symm
      _ ≤ kummerSeries lam₁ (1 / (4 * alpha₁)) -
            kummerSeries lam₂ (1 / (4 * alpha₁)) :=
        kummerSeries_lambda_first_gap
          lam₁ lam₂ (1 / (4 * alpha₁)) hlam₁ hleL (by positivity)
  have hα :
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
        kummerSeries lam₂ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂)) :=
    kummerSeries_alpha_first_gap
      lam₂ alpha₁ alpha₂ hlam₂ ha₁ ha₂ hleA
  linarith

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_quantitative_gap

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Mixed parameter first-excited quantitative gap for the genuine
basis-independent analytic Gaussian-Fock S₂ energy. -/
theorem C_intrinsicEntire_HS_energy_mixed_quantitative_gap
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) -
    (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha₁ hlam₁ ha₁ b₁,
      C_intrinsicEntire_HS_energy_eq_kummer
        lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂]
  exact KummerCoefficients.kummerSeries_mixed_quantitative_gap
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA

/-- The identical mixed quantitative gap for the genuine
source-Gram real diagonal traces on unrelated complete Hilbert bases. -/
theorem C_intrinsicEntire_Gram_trace_mixed_quantitative_gap
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    (∑' i : ι₁, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i)) (b₁ i))) -
    (∑' i : ι₂, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i))
      (b₂ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
        lam₁ alpha₁ hlam₁ ha₁ b₁,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer
        lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂]
  exact KummerCoefficients.kummerSeries_mixed_quantitative_gap
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_quantitative_gap
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_quantitative_gap

end GegenbauerFock.GeneralUltrasphericalFock
