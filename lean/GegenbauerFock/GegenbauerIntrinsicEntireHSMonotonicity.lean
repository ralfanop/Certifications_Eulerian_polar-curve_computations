import GegenbauerFock.GegenbauerIntrinsicEntireHSRealGammaIntegral
import GegenbauerFock.KummerPositiveBounds

/-!
# V007 — exact monotonicity in the Gaussian scale α

The true Gaussian entire-Fock Hilbert–Schmidt energy is the unregularized
Kummer function with argument t = 1/(4α). Positivity of every
ultraspherical even moment implies monotonicity of its full infinite
nonnegative series for t ≥ 0; the parameter map α ↦ 1/(4α)
reverses the order on α > 0.

This transfers to the analytic Fock S₂ energy and actual intrinsic
source-Gram diagonal trace on ANY complete source Hilbert basis.
No finite truncation or unverified special-function API is used.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The actual entire real Kummer series is monotone on nonnegative
real arguments, by comparing the summable terms coefficientwise. -/
theorem kummerSeries_mono_of_nonneg
    (lam s t : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (hst : s ≤ t) :
    kummerSeries lam s ≤ kummerSeries lam t := by
  have ht : 0 ≤ t := le_trans hs hst
  have hleft := kummerSeries_summable lam s hlam hs
  have hright := kummerSeries_summable lam t hlam ht
  have hterms (n : ℕ) :
      ratio lam n * (s ^ n / (Nat.factorial n : ℝ)) ≤
      ratio lam n * (t ^ n / (Nat.factorial n : ℝ)) := by
    have hp : s ^ n ≤ t ^ n := by gcongr
    apply mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hp (by positivity))
      (ratio_nonneg lam hlam n)
  unfold kummerSeries
  exact hleft.tsum_le_tsum hterms hright

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mono_of_nonneg

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Increasing the Gaussian width α decreases the actual analytic
Fock Hilbert–Schmidt energy, on any complete source Hilbert basis. -/
theorem C_intrinsicEntire_HS_energy_antitone_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (halpha : alpha₁ ≤ alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b i)‖ ^ 2) ≤
      ∑' i : ι, ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b i)‖ ^ 2 := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₂ hlam ha₂ b,
    C_intrinsicEntire_HS_energy_eq_kummer lam alpha₁ hlam ha₁ b]
  have ht : (0 : ℝ) ≤ 1 / (4 * alpha₂) := by positivity
  have hparam : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * alpha₁) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [halpha]
  exact KummerCoefficients.kummerSeries_mono_of_nonneg
    lam (1 / (4 * alpha₂)) (1 / (4 * alpha₁)) hlam ht hparam

/-- The true intrinsic source-Gram trace obeys the same monotonicity,
independently of the source Hilbert basis used to express its trace. -/
theorem C_intrinsicEntire_Gram_trace_antitone_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (halpha : alpha₁ ≤ alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
      RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b i)) (b i))) ≤
      ∑' i : ι,
        RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b i)) (b i)) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₂ hlam ha₂ b,
    C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₁ hlam ha₁ b]
  have ht : (0 : ℝ) ≤ 1 / (4 * alpha₂) := by positivity
  have hparam : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * alpha₁) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [halpha]
  exact KummerCoefficients.kummerSeries_mono_of_nonneg
    lam (1 / (4 * alpha₂)) (1 / (4 * alpha₁)) hlam ht hparam

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_antitone_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_antitone_alpha

end GegenbauerFock.GeneralUltrasphericalFock
