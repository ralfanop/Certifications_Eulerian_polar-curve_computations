import SpecialImaginaryPoint.V14119Priority3FredholmReciprocalPoleOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order

/-!
# Priority 3 — exact simple-zero/simple-pole criterion for the TRUE universal Fredholm determinant

For any arbitrary complex CFC Schatten-S₁ trace-class Hilbert operator T,
let f_T(z)=det_F(I+zT) be the actual universal Hilbert-compression-limit
Fredholm determinant. It is entire and normalized by f_T(0)=1.

At a complex spectral parameter z, the genuine Fredholm zero is SIMPLE
if and only if f_T(z)=0 and f_T'(z)≠0. At every such simple zero the
meromorphic reciprocal has exact meromorphic order -1, i.e. a simple
pole. These results hold without operator normality or selfadjointness.

This does not assert eigenvalue algebraic multiplicity or a resolvent
equivalence, which require separate spectral-theoretic arguments.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmSimpleSpectralZeros

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.FredholmReciprocalPoleOrder

/-- Genuine universal Fredholm determinant has analytic order one
exactly when the actual determinant vanishes and its complex
spectral derivative is nonzero. -/
theorem universalFredholm_simpleZero_iff
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    analyticOrderAt (fredholmDet T) z = 1 ↔
      fredholmDet T z = 0 ∧ deriv (fredholmDet T) z ≠ 0 := by
  simpa [iteratedDeriv_one, iteratedDeriv_zero] using
    (((universal_fredholmDet_entire T).analyticAt z)
      .analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := 1))

/-- A genuine zero with nonvanishing spectral derivative is a
simple analytic zero of the true universal operatorial determinant. -/
theorem universalFredholm_simpleZero_of_deriv_ne_zero
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0)
    (hd : deriv (fredholmDet T) z ≠ 0) :
    analyticOrderAt (fredholmDet T) z = 1 :=
  (universalFredholm_simpleZero_iff T z).mpr ⟨hz, hd⟩

/-- At every simple genuine universal Fredholm determinant zero,
the meromorphic reciprocal has EXACT simple-pole order -1. -/
theorem universalFredholmReciprocal_simplePole_at_simpleZero
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : analyticOrderAt (fredholmDet T) z = 1) :
    meromorphicOrderAt ((fredholmDet T)⁻¹) z =
      -((1 : ℤ) : WithTop ℤ) := by
  rw [universalFredholmReciprocal_order_eq, hz]
  simp

#print axioms Manuscript14Priority3.FredholmSimpleSpectralZeros.universalFredholm_simpleZero_iff
#print axioms Manuscript14Priority3.FredholmSimpleSpectralZeros.universalFredholm_simpleZero_of_deriv_ne_zero
#print axioms Manuscript14Priority3.FredholmSimpleSpectralZeros.universalFredholmReciprocal_simplePole_at_simpleZero

end Manuscript14Priority3.FredholmSimpleSpectralZeros
