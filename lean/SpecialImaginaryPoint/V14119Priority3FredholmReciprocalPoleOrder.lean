import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLocalFactorization
import Mathlib.Analysis.Meromorphic.Order

/-!
# Priority 3 — exact pole multiplicity of the genuine universal Fredholm reciprocal

The genuine CFC Schatten-S₁ Fredholm determinant f_T(z) = det_F(I+zT)
of ANY complex trace-class Hilbert operator T is entire and satisfies
f_T(0)=1. Its zeros therefore have finite positive analytic multiplicity.

The global meromorphic reciprocal (f_T)⁻¹ has meromorphic order equal
to the NEGATIVE of the corresponding analytic order of f_T, everywhere
in the complex plane. In particular, every zero of f_T is a genuine
finite-order pole of the reciprocal with exact integer multiplicity.

No auxiliary finite matrix determinant, spectral enumeration,
selfadjointness or positivity hypothesis is introduced.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmReciprocalPoleOrder

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalFredholmZeroMultiplicity

/-- The complex meromorphic order of the TRUE universal Fredholm
reciprocal is the negative analytic order of the actual determinant. -/
theorem universalFredholmReciprocal_order_eq
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    meromorphicOrderAt ((fredholmDet T)⁻¹) z =
      -((analyticOrderAt (fredholmDet T) z).map (↑)) := by
  rw [meromorphicOrderAt_inv,
    ((universal_fredholmDet_entire T).analyticAt z).meromorphicOrderAt_eq]

/-- At every zero of the genuine infinite-dimensional Fredholm
determinant there is a STRICTLY POSITIVE natural pole multiplicity
whose negative is the reciprocal's exact meromorphic order. -/
theorem universalFredholmReciprocal_zero_has_finite_pole_order
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    ∃ n : ℕ, 0 < n ∧
      meromorphicOrderAt ((fredholmDet T)⁻¹) z =
        -((n : ℤ) : WithTop ℤ) := by
  obtain ⟨n, hnpos, hn⟩ :=
    universalFredholm_zero_has_positive_finite_order T z hz
  refine ⟨n, hnpos, ?_⟩
  rw [universalFredholmReciprocal_order_eq, hn]
  simp

#print axioms Manuscript14Priority3.FredholmReciprocalPoleOrder.universalFredholmReciprocal_order_eq
#print axioms Manuscript14Priority3.FredholmReciprocalPoleOrder.universalFredholmReciprocal_zero_has_finite_pole_order

end Manuscript14Priority3.FredholmReciprocalPoleOrder
