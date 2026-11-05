import GegenbauerFock.ConcreteFockRowEnergy
import GegenbauerFock.MomentEnergyIntegral

/-!
# V007: row-energy series expressed in genuine scalar integrals

This module upgrades the concrete, infinite-dimensional coefficient-row
formula to integrals of the actual ultraspherical moments. Every n-th
term is a scalar Bochner/Lebesgue integral over the *general parameter*
Beta-pushforward ultraspherical probability measure.

It does NOT exchange the sum with the integral, identify the summed
integrand with an exponential, or assert the equality with the abstract
Hilbert–Schmidt ideal norm. These are separate theorems to establish.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The exact row energy is an infinite sum of actual L² moment integrals,
for every λ>0 and α>0, with no unproved analytic interchange. -/
theorem rowEnergy_eq_tsum_integrals
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      ∑' n : ℕ, WeightedMoments.squareWeight alpha n *
        (∫ u : ℝ, ‖(u : ℂ) ^ n‖ ^ 2
          ∂(Ultraspherical.measure lam)) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [rowEnergy_eq]
  apply tsum_congr
  intro n
  rw [MomentEnergyIntegral.monomial_norm_sq_integral
    (Ultraspherical.measure lam) (ae_abs_le_one lam) n]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_tsum_integrals

end GegenbauerFock.GeneralUltrasphericalFock
