import GegenbauerFock.HSRightIdeal
import GegenbauerFock.ConcreteFockRowEnergy

/-!
# V007: input-Hilbert-basis invariance of concrete Fock coordinate energy

For the *actual* ultraspherical transform, Parseval holds for each
output coordinate against an arbitrary complete orthonormal Hilbert
basis of the source L² space. Finite sums of output-coordinate energies
are therefore independent of the chosen source Hilbert basis.

The exchange of the two infinite basis sums, and the identification
with a separately bundled Schatten S₂ ideal norm, remain separate
obligations. No finite-dimensionality assumption is made.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For every source Hilbert basis (possibly infinite and not countably
enumerated), the squared energy of the n-th genuine Fock row is exactly
the sum of its values on the source basis. -/
theorem C_row_any_basis_parseval
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (n : ℕ) :
    (∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  calc
    (∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
        ∑' i : ι,
          ‖WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam)
            alpha n (b i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [C_coefficient lam alpha hlam ha (b i) n]
    _ = ‖WeightedMoments.coefficient
          (Ultraspherical.measure lam) (ae_abs_le_one lam)
          alpha n‖ ^ 2 :=
        FockEnergy.weightedMoment_row_basis_energy
          (Ultraspherical.measure lam) (ae_abs_le_one lam)
          alpha ha b n
    _ = ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
          rw [C_row_eq lam alpha hlam ha n]

/-- Every finite output truncation has an input-basis-independent
squared Hilbert energy. This is an exact theorem for the concrete C,
not an assumption that the full Schatten ideal has been constructed. -/
theorem C_finite_rows_any_basis_energy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (s : Finset ℕ) :
    (∑ n ∈ s, ∑' i : ι, ‖C lam alpha hlam ha (b i) n‖ ^ 2) =
      ∑ n ∈ s, ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro n hn
  exact C_row_any_basis_parseval lam alpha hlam ha b n

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_row_any_basis_parseval
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_finite_rows_any_basis_energy

end GegenbauerFock.GeneralUltrasphericalFock
