import GegenbauerFock.RowEnergyIntegral
import GegenbauerFock.FockExponentialSeries
import GegenbauerFock.UltrasphericalMomentBounds
import GegenbauerFock.KummerPochhammer

/-!
# V007: actual ultraspherical even-moment generating function

The row energy of the concrete Gegenbauer--Fock operator is the
exponential generating function of the even moments of the actual
symmetric Beta-pushforward ultraspherical probability measure.

The second theorem identifies this value with the unregularized
Kummer series *provided* the independently required general even-moment
identity is proved.  Crucially that hypothesis is visible in its type;
this module does not silently postulate the missing moment identity.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Unconditional exact expression of the infinite-dimensional Fock
row energy through the actual general ultraspherical even moments. -/
theorem rowEnergy_eq_evenMoment_series
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      ∑' n : ℕ, Ultraspherical.evenMoment lam n *
        ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  rw [rowEnergy_eq_tsum_integrals]
  apply tsum_congr
  intro n
  have hint :
      (∫ u : ℝ, ‖(u : ℂ) ^ n‖ ^ 2
        ∂(Ultraspherical.measure lam)) =
      Ultraspherical.evenMoment lam n := by
    unfold Ultraspherical.evenMoment
    apply integral_congr_ae
    filter_upwards [] with u
    rw [FockExponentialSeries.norm_monomial_sq]
    rw [← pow_mul]
  rw [hint]
  simp only [WeightedMoments.squareWeight]
  ring

/-- The sole remaining scalar gap in the Kummer trace formula is the
exact ultraspherical moment identity. The assumption is *not*
certified by this theorem. -/
theorem rowEnergy_eq_kummerSeries_of_evenMoment_formula
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hm : ∀ n : ℕ,
      Ultraspherical.evenMoment lam n = KummerCoefficients.ratio lam n) :
    rowEnergy lam alpha hlam ha =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [rowEnergy_eq_evenMoment_series lam alpha hlam ha]
  unfold KummerCoefficients.kummerSeries
  apply tsum_congr
  intro n
  rw [hm n]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_evenMoment_series
#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_kummerSeries_of_evenMoment_formula

end GegenbauerFock.GeneralUltrasphericalFock
