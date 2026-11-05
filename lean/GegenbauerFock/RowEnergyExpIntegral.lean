import GegenbauerFock.RowEnergyTonelli
import GegenbauerFock.FockExponentialSeries

/-!
# V007 — exact Fock Hilbert row-energy integral identity

The concrete bounded and compact ultraspherical-to-Fock-coefficient
Hilbert operator C_{λ,α} has squared canonical output row energy

  ∑_n ‖(coordinate_n ∘ C)‖²
      = ∫_{[-1,1]} exp(u²/(4α)) dν_λ(u).

This is an exact infinite-dimensional, mathematically meaningful
Hilbert–Schmidt row-energy identity: no finite cutoff, no uncertified
interchange, and no additional axioms.

The equivalence between this canonical row-energy and a separately
defined Schatten/Hilbert–Schmidt ideal norm and the identification with
the analytic Gaussian holomorphic function model remain distinct tasks.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact ultraspherical exponential integral formula for the canonical
Hilbert coefficient-row energy of the concrete compact operator. -/
theorem rowEnergy_eq_exp_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
        ∂(Ultraspherical.measure lam) := by
  rw [rowEnergy_eq_integral_series]
  simp_rw [FockExponentialSeries.energy_series_eq_exp]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_exp_integral

end GegenbauerFock.GeneralUltrasphericalFock
