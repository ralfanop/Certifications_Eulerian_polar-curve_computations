import SpecialImaginaryPoint.V14119Priority3FiniteFredholmZeroDivisor
import SpecialImaginaryPoint.V14119Priority3CountableUniversalSpectralZeros
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Priority 3 — a dense set of admissible circle radii for universal Fredholm contours

For ANY complex CFC Schatten-S₁ Hilbert operator T, including
nonnormal and nonselfadjoint operators, the actual infinite-dimensional
universal Hilbert-compression Fredholm determinant
  f_T(z) = det_F(I + zT)
has at most countably many complex zeros.

Their real-valued radii |z| form a countable set. Thus there is a
DENSE set of real radii r such that the entire complex circle |z|=r
contains NO zero of f_T. These are the exact admissible boundary
radii for later argument-principle/Jensen contour integrals.

No claim about an argument-principle integral is made in this module.
-/

noncomputable section

namespace Manuscript14Priority3.AdmissibleContourRadii

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.LocallyFiniteFredholmZeroSet
open Manuscript14Priority3.CountableUniversalSpectralZeros

/-- Radii of actual Fredholm determinant zeros, potentially including
zero but with no artificially inserted spectral values. -/
def universalFredholmZeroRadiusSet
    (T : ProbabilisticTheory.TraceClass H) : Set ℝ :=
  (fun z : ℂ => ‖z‖) '' universalFredholmZeroSet T

/-- The excluded circle radii of the genuine universal Fredholm
zero divisor form a countable set of real numbers. -/
theorem universalFredholmZeroRadiusSet_countable
    (T : ProbabilisticTheory.TraceClass H) :
    (universalFredholmZeroRadiusSet T).Countable := by
  exact (universalFredholmZeroSet_countable T).image (fun z : ℂ => ‖z‖)

/-- The set of admissible radius values avoiding ALL genuine
Fredholm determinant zeros on the corresponding complex circle
is DENSE on the entire real line. -/
theorem universalFredholm_admissibleContourRadii_dense
    (T : ProbabilisticTheory.TraceClass H) :
    Dense (universalFredholmZeroRadiusSet T)ᶜ := by
  exact (universalFredholmZeroRadiusSet_countable T).dense_compl ℝ

/-- Every complex circle with radius outside the countable
exceptional radius set is free of universal Fredholm zeros. -/
theorem universalFredholm_nonzero_on_admissible_circle
    (T : ProbabilisticTheory.TraceClass H) (r : ℝ)
    (hr : r ∈ (universalFredholmZeroRadiusSet T)ᶜ) :
    ∀ z : ℂ, ‖z‖ = r → fredholmDet T z ≠ 0 := by
  intro z hz hzero
  have hzmem : z ∈ universalFredholmZeroSet T := hzero
  have hrmem : r ∈ universalFredholmZeroRadiusSet T := by
    exact ⟨z, hzmem, hz⟩
  exact hr hrmem

#print axioms Manuscript14Priority3.AdmissibleContourRadii.universalFredholmZeroRadiusSet_countable
#print axioms Manuscript14Priority3.AdmissibleContourRadii.universalFredholm_admissibleContourRadii_dense
#print axioms Manuscript14Priority3.AdmissibleContourRadii.universalFredholm_nonzero_on_admissible_circle

end Manuscript14Priority3.AdmissibleContourRadii
