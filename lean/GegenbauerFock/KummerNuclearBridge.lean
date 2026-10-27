import GegenbauerFock.GramNuclearTrace
import GegenbauerFock.UltrasphericalKummerBridge

/-!
# V007: positive nuclear Gram mass as ultraspherical moments

This identifies the *actual positive rank-one operator presentation*
of the infinite-dimensional Gram map with a scalar even-moment
generating series. A separately defined canonical Schatten S₁ trace
is NOT assumed. The Kummer evaluation remains conditional solely on
the general ultraspherical even-moment formula.
-/

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Absolute operator-norm mass of the genuine Gram nuclear presentation
is exactly the exponential generating series of the true even moments. -/
theorem gramNuclearMass_eq_evenMoment_series
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∑' n : ℕ, Ultraspherical.evenMoment lam n *
        ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_evenMoment_series lam alpha hlam ha

/-- Under the *explicit* pending exact moment formula, the concrete
positive nuclear Gram mass equals the real unregularized Kummer series.
This theorem does not assert an abstract Schatten trace norm equality. -/
theorem gramNuclearMass_eq_kummerSeries_of_evenMoment_formula
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hm : ∀ n : ℕ,
      Ultraspherical.evenMoment lam n = KummerCoefficients.ratio lam n) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_kummerSeries_of_evenMoment_formula lam alpha hlam ha hm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_evenMoment_series
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_kummerSeries_of_evenMoment_formula

end GegenbauerFock.GeneralUltrasphericalFock
