import SpecialImaginaryPoint.V14119Priority3FredholmLinearJensenGrowth
import SpecialImaginaryPoint.V14119Priority3FredholmDivisorFinsum

/-!
# Priority 3 — a dimension-free linear Jensen bound for the ACTUAL finite Fredholm zero count

The genuine universal CFC Schatten-S₁ determinant f_T(z)=det_F(I+zT)
has been independently formalized in Lean as a compression limit.
A finite Finset of its actual complex spectral zeros within the
closed disk |z|≤r was constructed together with their strictly
positive finite analytic multiplicities.

The classical integer-valued meromorphic divisor of f_T on the
disk has also been proved to sum to *exactly* this natural-valued
finite multiplicity count. Separately, a true trace-norm global
Fredholm growth estimate and classical Jensen inequality prove
a linear bound on the meromorphic divisor sum.

This module joins those two certified results, thereby giving the
same LINEAR inequality directly for the previously constructed
finite, natural-number-valued count of true operatorial Fredholm zeros:

  N_T(r) ≤ 2 R ‖T‖ / log(R/r),  0<r<R,

and at the concrete doubling scale

  N_T(r) ≤ 4 r ‖T‖ / log 2.

Neither eigenvalue enumeration nor operator normality,
selfadjointness, positivity, finite rank or an abstract scalar-product
replacement is assumed. Jensen's classical theorem is not claimed new.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmMultiplicityLinearJensen

open Filter Topology Set Metric MeromorphicOn
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FiniteFredholmZeroDivisor
open Manuscript14Priority3.FredholmDivisorFinsum
open Manuscript14Priority3.FredholmLinearJensenGrowth

/-- For any complex trace-class T and 0<r<R, the *true finite
natural analytic-multiplicity count of actual Fredholm zeros*
inside the closed disk |z|≤r has an explicit linear-in-‖T‖ bound. -/
theorem universalFredholm_totalMultiplicity_linear_traceNorm_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (universalFredholm_closedDisk_totalMultiplicity T r : ℝ) ≤
      2 * (R * ‖T‖) / Real.log (R / r) := by
  have h :=
    universalFredholm_Jensen_zero_count_linear_traceNorm_bound T hr hrR
  rw [universalFredholm_divisor_finsum_eq_totalMultiplicity T r] at h
  simpa only [Int.cast_natCast] using h

/-- A completely explicit multiplicity count at the doubling
spectral radius: N_T(r) ≤ (4/log 2) r ‖T‖. -/
theorem universalFredholm_totalMultiplicity_doubling_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r : ℝ} (hr : 0 < r) :
    (universalFredholm_closedDisk_totalMultiplicity T r : ℝ) ≤
      (4 * r * ‖T‖) / Real.log 2 := by
  have h :=
    universalFredholm_Jensen_zero_count_double_radius T hr
  rw [universalFredholm_divisor_finsum_eq_totalMultiplicity T r] at h
  simpa only [Int.cast_natCast] using h

#print axioms Manuscript14Priority3.FredholmMultiplicityLinearJensen.universalFredholm_totalMultiplicity_linear_traceNorm_bound
#print axioms Manuscript14Priority3.FredholmMultiplicityLinearJensen.universalFredholm_totalMultiplicity_doubling_bound

end Manuscript14Priority3.FredholmMultiplicityLinearJensen
