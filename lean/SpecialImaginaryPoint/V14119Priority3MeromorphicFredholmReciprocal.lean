import SpecialImaginaryPoint.V14119Priority3HolomorphicFredholmReciprocal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Priority 3 — global meromorphic reciprocal of the genuine universal Fredholm determinant

For every actual (possibly nonnormal, nonselfadjoint) complex CFC Schatten-S₁
Hilbert operator T, the reciprocal of the true Hilbert-compression-limit
Fredholm determinant det_F(I+zT) is MEROMORPHIC on the whole complex plane.

This statement is global, allowing poles at determinant zeros. It is
stronger than mere holomorphy restricted to the open dense nonzero set.

The proof first upgrades the previously certified unconditional complex
differentiability of the genuine determinant to analytic-on-neighborhood
via the complex Cauchy theorem in Mathlib, then uses its exact theorem
that meromorphic functions are closed under pointwise inversion.
-/

noncomputable section

namespace Manuscript14Priority3.MeromorphicFredholmReciprocal

open Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire

/-- The actual universal CFC-S₁ Fredholm determinant is analytic
in a neighborhood of every complex spectral shift. -/
theorem universalFredholmDet_analyticOnNhd
    (T : ProbabilisticTheory.TraceClass H) :
    AnalyticOnNhd ℂ (fredholmDet T) (Set.univ : Set ℂ) := by
  intro z _hz
  exact (universal_fredholmDet_entire T).analyticAt z

/-- Global meromorphy of the reciprocal of the ACTUAL universal
infinite-dimensional trace-class Fredholm determinant. -/
theorem universalFredholmReciprocal_meromorphicOn
    (T : ProbabilisticTheory.TraceClass H) :
    MeromorphicOn (fun z : ℂ => (fredholmDet T z)⁻¹)
      (Set.univ : Set ℂ) := by
  simpa only [Pi.inv_apply] using
    (universalFredholmDet_analyticOnNhd T).meromorphicOn.inv

#print axioms Manuscript14Priority3.MeromorphicFredholmReciprocal.universalFredholmDet_analyticOnNhd
#print axioms Manuscript14Priority3.MeromorphicFredholmReciprocal.universalFredholmReciprocal_meromorphicOn

end Manuscript14Priority3.MeromorphicFredholmReciprocal
