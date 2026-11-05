import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaQuantitative
import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaStrictIdentifiability

/-!
# V007 — inverse stability of the ultraspherical source parameter

On a bounded positive ultraspherical-parameter interval (0,L], the
genuine Gaussian-Fock Hilbert–Schmidt squared energy, and the
intrinsic source-Gram diagonal trace, determine lambda with an explicit
global inverse Lipschitz constant 8*alpha*(L+1)^2.

This result compares scalar complete-basis invariants on two different
source Hilbert spaces. No operator norm comparison between different
Hilbert domains is asserted.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Ordered inverse stability obtained directly from the certified
first-excited-coefficient quantitative gap. -/
theorem kummerSeries_lambda_inverse_stability_ordered
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha) :
    lam₂ - lam₁ ≤
      8 * alpha * (L + 1) ^ 2 *
        (kummerSeries lam₁ (1 / (4 * alpha)) -
         kummerSeries lam₂ (1 / (4 * alpha))) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hle
  have hgap :
      (lam₂ - lam₁) /
          (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) ≤
        kummerSeries lam₁ (1 / (4 * alpha)) -
        kummerSeries lam₂ (1 / (4 * alpha)) := by
    calc
      (lam₂ - lam₁) /
          (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) =
        (ratio lam₁ 1 - ratio lam₂ 1) * (1 / (4 * alpha)) :=
          (ratio_lambda_first_gap_gaussian_exact
            lam₁ lam₂ alpha hlam₁ hlam₂ ha).symm
      _ ≤ kummerSeries lam₁ (1 / (4 * alpha)) -
            kummerSeries lam₂ (1 / (4 * alpha)) :=
          kummerSeries_lambda_first_gap
            lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)
  have hden : 0 < 8 * alpha * (lam₁ + 1) * (lam₂ + 1) := by positivity
  have hdiff : 0 ≤
      kummerSeries lam₁ (1 / (4 * alpha)) -
      kummerSeries lam₂ (1 / (4 * alpha)) :=
    (div_nonneg (sub_nonneg.mpr hle) hden.le).trans hgap
  have hLpos : 0 ≤ L + 1 := by linarith
  have hlam₂pos : 0 ≤ lam₂ + 1 := by linarith
  have hprod : (lam₁ + 1) * (lam₂ + 1) ≤ (L + 1) ^ 2 := by
    calc
      (lam₁ + 1) * (lam₂ + 1) ≤
          (L + 1) * (lam₂ + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hlam₂pos
      _ ≤ (L + 1) * (L + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hLpos
      _ = (L + 1) ^ 2 := by ring
  have hdenbound :
      8 * alpha * (lam₁ + 1) * (lam₂ + 1) ≤
        8 * alpha * (L + 1) ^ 2 := by
    calc
      8 * alpha * (lam₁ + 1) * (lam₂ + 1) =
          (8 * alpha) * ((lam₁ + 1) * (lam₂ + 1)) := by ring
      _ ≤ (8 * alpha) * (L + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
  calc
    lam₂ - lam₁ ≤
        (kummerSeries lam₁ (1 / (4 * alpha)) -
         kummerSeries lam₂ (1 / (4 * alpha))) *
            (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) :=
      (div_le_iff₀ hden).mp hgap
    _ ≤ (kummerSeries lam₁ (1 / (4 * alpha)) -
          kummerSeries lam₂ (1 / (4 * alpha))) *
            (8 * alpha * (L + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hdenbound hdiff
    _ = 8 * alpha * (L + 1) ^ 2 *
          (kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))) := by ring

/-- Global inverse Lipschitz stability of unregularized Kummer mass
on any bounded positive λ interval, with fixed Gaussian width alpha. -/
theorem kummerSeries_lambda_inverse_stability
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha) :
    |lam₁ - lam₂| ≤
      8 * alpha * (L + 1) ^ 2 *
        |kummerSeries lam₁ (1 / (4 * alpha)) -
         kummerSeries lam₂ (1 / (4 * alpha))| := by
  rcases le_total lam₁ lam₂ with hle | hle
  · have hbound :=
      kummerSeries_lambda_inverse_stability_ordered
        lam₁ lam₂ L alpha hlam₁ hle hL₁ hL₂ ha
    have hmono :=
      kummerSeries_antitone_lambda
        lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)
    calc
      |lam₁ - lam₂| = lam₂ - lam₁ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      _ ≤ 8 * alpha * (L + 1) ^ 2 *
          (kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))) := hbound
      _ = 8 * alpha * (L + 1) ^ 2 *
          |kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  · have hbound :=
      kummerSeries_lambda_inverse_stability_ordered
        lam₂ lam₁ L alpha hlam₂ hle hL₂ hL₁ ha
    have hmono :=
      kummerSeries_antitone_lambda
        lam₂ lam₁ (1 / (4 * alpha)) hlam₂ hle (by positivity)
    calc
      |lam₁ - lam₂| = lam₁ - lam₂ :=
        abs_of_nonneg (sub_nonneg.mpr hle)
      _ ≤ 8 * alpha * (L + 1) ^ 2 *
          (kummerSeries lam₂ (1 / (4 * alpha)) -
           kummerSeries lam₁ (1 / (4 * alpha))) := hbound
      _ = 8 * alpha * (L + 1) ^ 2 *
          |kummerSeries lam₁ (1 / (4 * alpha)) -
           kummerSeries lam₂ (1 / (4 * alpha))| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
        ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_lambda_inverse_stability_ordered
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_lambda_inverse_stability

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Explicit inverse Lipschitz stability in λ of actual basis-defined
analytic Gaussian-Fock Hilbert–Schmidt squared energies. The source
Hilbert bases may have different index types and different domains. -/
theorem C_intrinsicEntire_HS_energy_lambda_inverse_stability
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    |lam₁ - lam₂| ≤ 8 * alpha * (L + 1) ^ 2 *
      |(∑' i : ι₁, ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) -
       (∑' i : ι₂, ‖C_intrinsicEntire lam₂ alpha hlam₂ ha (b₂ i)‖ ^ 2)| := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha hlam₁ ha b₁,
    C_intrinsicEntire_HS_energy_eq_kummer lam₂ alpha hlam₂ ha b₂]
  exact KummerCoefficients.kummerSeries_lambda_inverse_stability
    lam₁ lam₂ L alpha hlam₁ hlam₂ hL₁ hL₂ ha

/-- The corresponding inverse Lipschitz estimate for the genuine
intrinsic source-Gram real diagonal traces across different Hilbert bases. -/
theorem C_intrinsicEntire_Gram_trace_lambda_inverse_stability
    (lam₁ lam₂ L alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hL₁ : lam₁ ≤ L) (hL₂ : lam₂ ≤ L) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    |lam₁ - lam₂| ≤ 8 * alpha * (L + 1) ^ 2 *
      |(∑' i : ι₁, RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) -
       (∑' i : ι₂, RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam₂ alpha hlam₂ ha (b₂ i)) (b₂ i)))| := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha hlam₁ ha b₁,
    C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₂ alpha hlam₂ ha b₂]
  exact KummerCoefficients.kummerSeries_lambda_inverse_stability
    lam₁ lam₂ L alpha hlam₁ hlam₂ hL₁ hL₂ ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_lambda_inverse_stability
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_lambda_inverse_stability

end GegenbauerFock.GeneralUltrasphericalFock
