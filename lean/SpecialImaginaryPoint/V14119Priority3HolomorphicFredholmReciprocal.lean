import SpecialImaginaryPoint.V14119Priority3FredholmZeroSetNullity

/-!
# Priority 3 — holomorphic reciprocal of the genuine CFC S₁ Fredholm determinant

For every genuine trace-class complex Hilbert operator T, the function
  z ↦ (det_F(I+zT))⁻¹
is complex differentiable at every shift with nonvanishing genuine
universal Fredholm determinant. Thus it is holomorphic on the open
dense nonzero spectral-parameter set, without normality or
selfadjointness assumptions. The zero set itself may be nonempty.

The argument uses only the certified *entire* Hilbert-compression
Fredholm determinant and the analytic inversion rule.
-/

noncomputable section

namespace Manuscript14Priority3.HolomorphicFredholmReciprocal

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.GenericFredholmSpectralParameters

/-- At each nonzero spectral shift the reciprocal of the actual
infinite-dimensional Fredholm determinant is complex differentiable. -/
theorem universalFredholmReciprocal_differentiableAt
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => (fredholmDet T w)⁻¹) z := by
  exact (universal_fredholmDet_entire T z).inv hz

/-- The genuine universal Fredholm reciprocal is holomorphic on
the entire OPEN DENSE complex nonzero spectral-parameter set. -/
theorem universalFredholmReciprocal_differentiableOn
    (T : ProbabilisticTheory.TraceClass H) :
    DifferentiableOn ℂ (fun z : ℂ => (fredholmDet T z)⁻¹)
      (universalFredholmNonzeroSet T) := by
  intro z hz
  exact (universalFredholmReciprocal_differentiableAt T z
    ((mem_universalFredholmNonzeroSet_iff T z).mp hz)).differentiableWithinAt

#print axioms Manuscript14Priority3.HolomorphicFredholmReciprocal.universalFredholmReciprocal_differentiableAt
#print axioms Manuscript14Priority3.HolomorphicFredholmReciprocal.universalFredholmReciprocal_differentiableOn

end Manuscript14Priority3.HolomorphicFredholmReciprocal
