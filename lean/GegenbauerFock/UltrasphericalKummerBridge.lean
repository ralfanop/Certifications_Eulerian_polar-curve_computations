import GegenbauerFock.RowEnergyExpIntegral
import GegenbauerFock.FockExponentialSeries
import GegenbauerFock.UltrasphericalMomentBounds
import GegenbauerFock.KummerPochhammer
import GegenbauerFock.UltrasphericalBetaMoments

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

/-- Unconditional exact Kummer evaluation of the squared canonical
Hilbert--Schmidt coordinate-row energy for the concrete infinite
Gegenbauer--Fock Hilbert operator, for every λ>0 and α>0.

Unlike the preceding conditional bridge, the beta moment quotient
is now proved from the normalized symmetric beta measure. -/
theorem rowEnergy_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  exact rowEnergy_eq_kummerSeries_of_evenMoment_formula
    lam alpha hlam ha (Ultraspherical.evenMoment_eq_ratio lam hlam)

/-- A genuine ultraspherical exponential integral is exactly the
unregularized Kummer power series. This is an analytic identity,
not an equality with an unverified regularized ₁F₁ convention. -/
theorem exp_integral_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
      ∂(Ultraspherical.measure lam)) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [← rowEnergy_eq_exp_integral lam alpha hlam ha]
  exact rowEnergy_eq_kummerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_kummerSeries
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exp_integral_eq_kummerSeries

/-- Fully explicit Gauss--Kummer hypergeometric series identity for
the squared canonical Hilbert--Schmidt row energy of C_{λ,α}.
The rising Pochhammer polynomials are exactly Mathlib's
`ascPochhammer`, not a merely recursively named ratio. -/
theorem rowEnergy_eq_pochhammerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      ∑' n : ℕ,
        ((ascPochhammer ℝ n).eval (1 / 2) /
          (ascPochhammer ℝ n).eval (lam + 1)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  rw [rowEnergy_eq_kummerSeries lam alpha hlam ha,
    KummerCoefficients.kummerSeries_eq_pochhammer
      lam (1 / (4 * alpha)) hlam]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_pochhammerSeries

/-- The *concrete bounded operator* C has canonical squared
Hilbert--Schmidt coordinate-row energy equal to the Kummer value,
expressed directly through the independent FockEnergy API rather
than only the specialized ultraspherical shorthand. This is a
canonical-target-row formulation; basis-independent Schatten S₂
norm remains a separate formal obligation. -/
theorem concreteFock_squaredRowEnergy_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      FockEnergy.squaredRowEnergy (Ultraspherical.measure lam)
        (C lam alpha hlam ha)) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  change rowEnergy lam alpha hlam ha =
    KummerCoefficients.kummerSeries lam (1 / (4 * alpha))
  exact rowEnergy_eq_kummerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.concreteFock_squaredRowEnergy_eq_kummerSeries

end GegenbauerFock.GeneralUltrasphericalFock
