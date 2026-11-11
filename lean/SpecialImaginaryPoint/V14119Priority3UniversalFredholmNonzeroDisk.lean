import SpecialImaginaryPoint.V14119Priority3FredholmReciprocalPoleOrder
import Mathlib.Topology.MetricSpace.Basic

/-!
# Priority 3 — a zero-free disk for every universal CFC-S₁ Fredholm determinant

For each complex Schatten-S₁ trace-class Hilbert operator T, the
genuine universal Hilbert-compression Fredholm determinant has
normalization det_F(I+0T)=1. Together with its genuine entire
holomorphy, this yields a strictly positive radius around z=0
without any determinant zeros. In particular, each zero has its
absolute spectral parameter bounded below by a T-dependent
positive real number.

No uniform-in-T or explicit optimal-radius estimate is asserted.
No selfadjointness, positivity or normality hypothesis is used.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmNonzeroDisk

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.GenericFredholmSpectralParameters

/-- The actual universal trace-class Fredholm determinant does not
vanish at the origin of the spectral parameter plane. -/
theorem universalFredholmDet_nonzero_at_zero
    (T : ProbabilisticTheory.TraceClass H) :
    fredholmDet T 0 ≠ 0 := by
  rw [fredholmDet_zero]
  exact one_ne_zero

/-- For every genuine CFC trace-class operator T, there is an
OPEN DISK of positive radius around 0 on which its true universal
Fredholm determinant is everywhere nonzero. -/
theorem universalFredholmDet_exists_nonzero_disk
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, ‖z‖ < ε → fredholmDet T z ≠ 0 := by
  have h0 : (0 : ℂ) ∈ universalFredholmNonzeroSet T :=
    (mem_universalFredholmNonzeroSet_iff T 0).mpr
      (universalFredholmDet_nonzero_at_zero T)
  obtain ⟨ε, hε, hsub⟩ :=
    (Metric.isOpen_iff.mp (universalFredholmNonzeroSet_isOpen T)) 0 h0
  refine ⟨ε, hε, ?_⟩
  intro z hz
  apply (mem_universalFredholmNonzeroSet_iff T z).mp
  apply hsub
  simpa only [Metric.mem_ball, dist_zero_right] using hz

/-- Every actual spectral zero of the universal Fredholm determinant
lies OUTSIDE a common positive disk centered at zero (radius depends
on T). -/
theorem universalFredholmDet_zeros_bounded_away_from_zero
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, fredholmDet T z = 0 → ε ≤ ‖z‖ := by
  obtain ⟨ε, hε, hnonzero⟩ := universalFredholmDet_exists_nonzero_disk T
  refine ⟨ε, hε, ?_⟩
  intro z hz
  by_contra hnot
  have hzsmall : ‖z‖ < ε := lt_of_not_ge hnot
  exact hnonzero z hzsmall hz

#print axioms Manuscript14Priority3.UniversalFredholmNonzeroDisk.universalFredholmDet_nonzero_at_zero
#print axioms Manuscript14Priority3.UniversalFredholmNonzeroDisk.universalFredholmDet_exists_nonzero_disk
#print axioms Manuscript14Priority3.UniversalFredholmNonzeroDisk.universalFredholmDet_zeros_bounded_away_from_zero

end Manuscript14Priority3.UniversalFredholmNonzeroDisk
