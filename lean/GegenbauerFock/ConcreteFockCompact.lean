import GegenbauerFock.GeneralUltrasphericalFock
import GegenbauerFock.SummableRowsCompact

/-!
# V007: compactness of the actual ultraspherical-to-Fock coefficient operator

The proof is not an abstract "if compact then compact" instance:
it derives the needed summability of the actual coordinate rows of C
from the factorial bounds on weighted L² moments, then applies the
kernel-verified finite-rank convergence theorem.

This is compactness in the genuine infinite-dimensional coefficient
Hilbert-space model; it does not assert that an isometry to the
holomorphic Gaussian-integral Fock space has been formalized.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The n-th canonical row of the actual C operator is the
factorially weighted monomial moment functional. -/
theorem C_row_eq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    SummableRowsCompact.row (C lam alpha hlam ha) n =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      WeightedMoments.coefficient (Ultraspherical.measure lam)
        (ae_abs_le_one lam) alpha n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  apply ContinuousLinearMap.ext
  intro f
  exact C_coefficient lam alpha hlam ha f n

/-- The actual ultraspherical-Fock map has summable squared norms
of its canonical output-coordinate rows. -/
theorem C_rows_summable (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  have h := WeightedMoments.coefficient_norm_sq_summable
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha
  simpa only [C_row_eq] using h

/-- The **concrete** bounded Gegenbauer-Fock coefficient operator is
compact, with λ>0 and α>0, not merely conditionally compact. -/
theorem C_compact (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C lam alpha hlam ha) := by
  exact SummableRowsCompact.compact_of_summable_rows
    (C lam alpha hlam ha) (C_rows_summable lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_row_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_rows_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_compact

end GegenbauerFock.GeneralUltrasphericalFock
