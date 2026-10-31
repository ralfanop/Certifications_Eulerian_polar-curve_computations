import GegenbauerFock.RowEnergyIntegral
import GegenbauerFock.MomentSeriesIntegral

/-!
# V007 — actual Hilbert coefficient-row energy as a single scalar integral

Under λ>0, α>0, the row energy of the concrete bounded operator
L²(ν_λ) -> ℓ²(ℕ;ℂ) equals a single Lebesgue integral of the
factorial-weighted monomial series. Crucially this equality uses the
independently proved Fubini/Tonelli series-integral exchange.

The final identification with exp(u²/(4α)) and with the abstract
Hilbert–Schmidt ideal norm is not asserted in this file.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem rowEnergy_eq_integral_series
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      ∫ u : ℝ, (∑' n : ℕ, MomentSeriesIntegral.term alpha n u)
        ∂(Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [rowEnergy_eq_tsum_integrals]
  rw [MomentSeriesIntegral.integral_tsum_energy
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha]
  apply tsum_congr
  intro n
  simp only [MomentSeriesIntegral.term, integral_const_mul]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_integral_series

end GegenbauerFock.GeneralUltrasphericalFock
