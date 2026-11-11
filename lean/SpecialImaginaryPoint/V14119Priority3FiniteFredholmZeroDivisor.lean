import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLocalFactorization
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Analytic.Order

/-!
# Priority 3 — finite genuine Fredholm spectral zero divisor on closed disks

For any arbitrary complex CFC Schatten-S₁ trace-class Hilbert operator T,
consider the *actual* universal Fredholm determinant f_T(z)=det_F(I+zT).
Its zeros are closed and discrete, and only finitely many lie in a
bounded complex disk. By the independently kernel-certified positive
analytic-order theorem, each such spectral zero carries a strictly
positive finite integer multiplicity.

This module realizes a genuine finite spectral zero divisor on a disk
as a finite set, not an enumerated sequence of operator eigenvalues.
It prepares exact finite sums of analytic multiplicities for subsequent
argument-principle, contour-integral, and Jensen-formula formalizations.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteFredholmZeroDivisor

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.LocallyFiniteFredholmZeroSet
open Manuscript14Priority3.UniversalFredholmZeroMultiplicity

/-- Every bounded closed spectral disk contains finitely many zeros
of the genuine universal CFC-S₁ Fredholm determinant. -/
theorem universalFredholm_closedDisk_zeros_finite
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) :
    (Metric.closedBall (0 : ℂ) R ∩ universalFredholmZeroSet T).Finite := by
  exact universalFredholmZeroSet_bounded_inter_finite T
    (Metric.closedBall (0 : ℂ) R) Metric.isBounded_closedBall

/-- The finite set of ACTUAL infinite-dimensional Fredholm determinant
zeros in the complex closed disk centered at 0 of radius R. -/
noncomputable def universalFredholm_closedDisk_zeroFinset
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) : Finset ℂ :=
  (universalFredholm_closedDisk_zeros_finite T R).toFinset

/-- Exact characterization of the finite zero divisor support:
nothing is added or lost relative to the actual Fredholm zeros. -/
theorem mem_universalFredholm_closedDisk_zeroFinset_iff
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) (z : ℂ) :
    z ∈ universalFredholm_closedDisk_zeroFinset T R ↔
      ‖z‖ ≤ R ∧ fredholmDet T z = 0 := by
  simp [universalFredholm_closedDisk_zeroFinset,
    universalFredholmZeroSet, Metric.mem_closedBall, dist_zero_right]

/-- Every zero in the finite divisor support has positive finite
analytic multiplicity in the universal Fredholm determinant. -/
theorem universalFredholm_closedDisk_zeroMultiplicity_pos
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) (z : ℂ)
    (hz : z ∈ universalFredholm_closedDisk_zeroFinset T R) :
    0 < analyticOrderNatAt (fredholmDet T) z := by
  have hz0 : fredholmDet T z = 0 :=
    ((mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mp hz).2
  obtain ⟨n, hnpos, hn⟩ :=
    universalFredholm_zero_has_positive_finite_order T z hz0
  have hn' : analyticOrderNatAt (fredholmDet T) z = n := by
    simp [analyticOrderNatAt, hn]
  simpa only [hn'] using hnpos

/-- Total finite analytic multiplicity of actual Fredholm zeros
inside a closed disk. The number is well-defined without choosing
an eigenvalue enumeration or a normality hypothesis. -/
noncomputable def universalFredholm_closedDisk_totalMultiplicity
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) : ℕ :=
  ∑ z ∈ universalFredholm_closedDisk_zeroFinset T R,
    analyticOrderNatAt (fredholmDet T) z

#print axioms Manuscript14Priority3.FiniteFredholmZeroDivisor.universalFredholm_closedDisk_zeros_finite
#print axioms Manuscript14Priority3.FiniteFredholmZeroDivisor.mem_universalFredholm_closedDisk_zeroFinset_iff
#print axioms Manuscript14Priority3.FiniteFredholmZeroDivisor.universalFredholm_closedDisk_zeroMultiplicity_pos

end Manuscript14Priority3.FiniteFredholmZeroDivisor
