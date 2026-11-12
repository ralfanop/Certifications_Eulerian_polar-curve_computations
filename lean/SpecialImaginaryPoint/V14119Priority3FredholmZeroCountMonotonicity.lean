import SpecialImaginaryPoint.V14119Priority3FiniteFredholmZeroDivisor

/-!
# Priority 3 — monotone zero count with analytic multiplicity for true Fredholm determinants

For arbitrary complex CFC Schatten-S₁ Hilbert trace-class operator T, its genuine
universal Hilbert-compression-limit Fredholm determinant has only finitely
many zeros in a bounded disk. Each carries a strictly positive, finite
analytic multiplicity.

This module constructs the monotonic zero-count function N_T(R) as a finite
sum of exact analytic orders, shows N_T(R) is monotone in the disk radius,
and proves that a nonempty spectral divisor contributes strictly positively.
No eigenvalue enumeration or operator normality is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmZeroCountMonotonicity

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FiniteFredholmZeroDivisor

/-- The true finite zero divisor support is monotone under increasing
radius of closed disks in the complex spectral-parameter plane. -/
theorem universalFredholm_closedDisk_zeroFinset_mono
    (T : ProbabilisticTheory.TraceClass H) {R S : ℝ}
    (hRS : R ≤ S) :
    universalFredholm_closedDisk_zeroFinset T R ⊆
      universalFredholm_closedDisk_zeroFinset T S := by
  intro z hz
  obtain ⟨hzR, hz0⟩ :=
    (mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mp hz
  exact (mem_universalFredholm_closedDisk_zeroFinset_iff T S z).mpr
    ⟨hzR.trans hRS, hz0⟩

/-- Number of genuine universal Fredholm determinant zeros, counted
with their exact analytic multiplicities, is NONDECREASING
as the closed disk radius increases. -/
theorem universalFredholm_closedDisk_totalMultiplicity_mono
    (T : ProbabilisticTheory.TraceClass H) {R S : ℝ}
    (hRS : R ≤ S) :
    universalFredholm_closedDisk_totalMultiplicity T R ≤
      universalFredholm_closedDisk_totalMultiplicity T S := by
  unfold universalFredholm_closedDisk_totalMultiplicity
  exact Finset.sum_le_sum_of_subset
    (universalFredholm_closedDisk_zeroFinset_mono T hRS)

/-- If a given closed disk has no genuine Fredholm determinant zero,
its analytic-multiplicity-weighted zero count is exactly zero. -/
theorem universalFredholm_closedDisk_totalMultiplicity_eq_zero_of_nonvanishing
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ)
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → fredholmDet T z ≠ 0) :
    universalFredholm_closedDisk_totalMultiplicity T R = 0 := by
  unfold universalFredholm_closedDisk_totalMultiplicity
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨hzR, hz0⟩ :=
    (mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mp hz
  exact (hzero z hzR hz0).elim

/-- Every ACTUAL zero inside a closed disk makes the total analytic
multiplicity of the true infinite-dimensional Fredholm zero divisor
strictly positive. -/
theorem universalFredholm_closedDisk_totalMultiplicity_pos_of_zero
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ)
    (z : ℂ) (hbound : ‖z‖ ≤ R)
    (hz : fredholmDet T z = 0) :
    0 < universalFredholm_closedDisk_totalMultiplicity T R := by
  have hzmem : z ∈ universalFredholm_closedDisk_zeroFinset T R :=
    (mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mpr
      ⟨hbound, hz⟩
  have hpos :=
    universalFredholm_closedDisk_zeroMultiplicity_pos T R z hzmem
  unfold universalFredholm_closedDisk_totalMultiplicity
  exact Finset.sum_pos' (fun w _ => Nat.zero_le _) ⟨z, hzmem, hpos⟩

#print axioms Manuscript14Priority3.FredholmZeroCountMonotonicity.universalFredholm_closedDisk_zeroFinset_mono
#print axioms Manuscript14Priority3.FredholmZeroCountMonotonicity.universalFredholm_closedDisk_totalMultiplicity_mono
#print axioms Manuscript14Priority3.FredholmZeroCountMonotonicity.universalFredholm_closedDisk_totalMultiplicity_eq_zero_of_nonvanishing
#print axioms Manuscript14Priority3.FredholmZeroCountMonotonicity.universalFredholm_closedDisk_totalMultiplicity_pos_of_zero

end Manuscript14Priority3.FredholmZeroCountMonotonicity
