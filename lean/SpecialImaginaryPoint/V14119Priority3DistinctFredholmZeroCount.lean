import SpecialImaginaryPoint.V14119Priority3FredholmMultiplicityLinearJensen

/-!
# Priority 3 — explicitly bounding DISTINCT genuine Fredholm zeros

We have constructed, for any complex CFC Schatten-S₁ trace-class
Hilbert operator T, the actual finite set of zeros in the closed
complex disk |z|≤r of the true universal compression-limit Fredholm
determinant f_T(z)=det_F(I+zT). Each zero has a strictly positive
natural analytic multiplicity, and the total multiplicity admits
a genuine dimension-independent linear trace-norm Jensen bound.

This module passes from counting zeros WITH multiplicity to counting
DISTINCT zeros. The new finite cardinality estimate is valid also for
nonnormal, nonselfadjoint operators, without any operator eigenvalue
enumeration or semisimplicity assumption.

Both the general 0<r<R and doubled-radius R=2r bounds are exact.
-/

noncomputable section

namespace Manuscript14Priority3.DistinctFredholmZeroCount

open Filter Topology Set Metric MeromorphicOn
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FiniteFredholmZeroDivisor
open Manuscript14Priority3.FredholmMultiplicityLinearJensen

/-- Each distinct genuine universal Fredholm zero contributes at
least one to the natural-number analytic-multiplicity total. -/
theorem universalFredholm_distinctZeroCount_le_totalMultiplicity
    (T : ProbabilisticTheory.TraceClass H) (r : ℝ) :
    (universalFredholm_closedDisk_zeroFinset T r).card ≤
      universalFredholm_closedDisk_totalMultiplicity T r := by
  classical
  have hsum :
      (∑ z ∈ universalFredholm_closedDisk_zeroFinset T r, (1 : ℕ)) ≤
        (∑ z ∈ universalFredholm_closedDisk_zeroFinset T r,
          analyticOrderNatAt (fredholmDet T) z) := by
    apply Finset.sum_le_sum
    intro z hz
    exact Nat.succ_le_iff.mpr
      (universalFredholm_closedDisk_zeroMultiplicity_pos T r z hz)
  simpa [universalFredholm_closedDisk_totalMultiplicity] using hsum

/-- The NUMBER OF DISTINCT genuine Fredholm determinant zeros in
the closed disk |z|≤r is bounded by 2 R ‖T‖/log(R/r)
for any 0<r<R. This does not require simple zeros. -/
theorem universalFredholm_distinctZeroCount_linear_traceNorm_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ((universalFredholm_closedDisk_zeroFinset T r).card : ℝ) ≤
      2 * (R * ‖T‖) / Real.log (R / r) := by
  have hcard :
      ((universalFredholm_closedDisk_zeroFinset T r).card : ℝ) ≤
        (universalFredholm_closedDisk_totalMultiplicity T r : ℝ) := by
    exact_mod_cast
      (universalFredholm_distinctZeroCount_le_totalMultiplicity T r)
  exact hcard.trans
    (universalFredholm_totalMultiplicity_linear_traceNorm_bound T hr hrR)

/-- An explicit bound at doubling scale on DISTINCT actual
universal Fredholm zeros in a closed complex disk: the finite
cardinality is at most 4r‖T‖/log 2. -/
theorem universalFredholm_distinctZeroCount_doubling_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r : ℝ} (hr : 0 < r) :
    ((universalFredholm_closedDisk_zeroFinset T r).card : ℝ) ≤
      (4 * r * ‖T‖) / Real.log 2 := by
  have hcard :
      ((universalFredholm_closedDisk_zeroFinset T r).card : ℝ) ≤
        (universalFredholm_closedDisk_totalMultiplicity T r : ℝ) := by
    exact_mod_cast
      (universalFredholm_distinctZeroCount_le_totalMultiplicity T r)
  exact hcard.trans
    (universalFredholm_totalMultiplicity_doubling_bound T hr)

#print axioms Manuscript14Priority3.DistinctFredholmZeroCount.universalFredholm_distinctZeroCount_le_totalMultiplicity
#print axioms Manuscript14Priority3.DistinctFredholmZeroCount.universalFredholm_distinctZeroCount_linear_traceNorm_bound
#print axioms Manuscript14Priority3.DistinctFredholmZeroCount.universalFredholm_distinctZeroCount_doubling_bound

end Manuscript14Priority3.DistinctFredholmZeroCount
