import GegenbauerFock.UltrasphericalGammaDensity
import GegenbauerFock.UltrasphericalOddVanishing
import GegenbauerFock.UltrasphericalKummerBridge

/-!
# V007 — Gamma-density moments and unregularized Kummer integral

This module connects the actual Gamma-normalized ultraspherical
Lebesgue density to the independently certified symmetric Beta moments
and to the unregularized Kummer series. All identities concern the
original real-line integral, not a formal moment functional.
The onto Gaussian holomorphic Bargmann–Fock isometry is separate.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- Exact even moments of the Gamma-normalized ultraspherical density. -/
theorem gammaDensity_evenMoment_eq_ratio
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (∫ u : ℝ, u ^ (2 * n)
      ∂((volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)))) =
      KummerCoefficients.ratio lam n := by
  rw [← measure_eq_withDensity_gamma lam hlam]
  exact evenMoment_eq_ratio lam hlam n

/-- Every odd moment of the same Gamma-normalized density vanishes. -/
theorem gammaDensity_oddMoment_eq_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (∫ u : ℝ, u ^ (2 * n + 1)
      ∂((volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)))) = 0 := by
  rw [← measure_eq_withDensity_gamma lam hlam]
  exact oddMoment_eq_zero lam hlam n

/-- The genuine Gamma-density exponential integral is exactly the
unregularized confluent hypergeometric Kummer series. -/
theorem gammaDensity_exp_integral_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
      ∂((volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)))) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [← measure_eq_withDensity_gamma lam hlam]
  exact GegenbauerFock.GeneralUltrasphericalFock.exp_integral_eq_kummerSeries
    lam alpha hlam ha

#print axioms GegenbauerFock.Ultraspherical.gammaDensity_evenMoment_eq_ratio
#print axioms GegenbauerFock.Ultraspherical.gammaDensity_oddMoment_eq_zero
#print axioms GegenbauerFock.Ultraspherical.gammaDensity_exp_integral_eq_kummerSeries

end GegenbauerFock.Ultraspherical
