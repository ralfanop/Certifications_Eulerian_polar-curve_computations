import GegenbauerFock.PhyslibTraceClassCompat

/-!
# V007: source-compatible Physlib infinite-dimensional Hilbert--Schmidt bridge

Selective port of the *definition* of
`ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt` from
`PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/HilbertSchmidt.lean`
by Tom Ole Diem, Apache-2.0. Upstream Physlib pins Lean 4 v4.35.0,
whereas V007 MUST retain v4.35.0-rc3 / pinned Mathlib 0272bbe.

The actual rectangular C : L²(νλ) → ℓ² is already certified in V007
as Hilbert--Schmidt on *every* complete source Hilbert basis.
The positive Gram G=C†C is an endomorphism, so it can also be shown
to satisfy the exact source-compatible Physlib IsHilbertSchmidt predicate.

This file does not pretend that Physlib's endomorphism notion is itself
a type for rectangular operators. No additional axioms.
-/

noncomputable section

namespace ProbabilisticTheory.HilbertSchmidt

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact port of the infinite-dimensional PhyslibAlpha S₂
membership predicate, based on summability in one complete basis. -/
def IsHilbertSchmidt (S : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H),
    Summable (fun i : w => ‖S (b i)‖ ^ 2)

end ProbabilisticTheory.HilbertSchmidt

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The concrete positive Gram C†C belongs to Physlib's
source-compatible infinite-dimensional S₂ class; the proof is derived
from the already certified rectangular Hilbert--Schmidt criterion
and the general bounded-left-composition ideal theorem. -/
theorem gram_isPhyslibHilbertSchmidt
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      (gram lam alpha hlam ha) := by
  let H := Lp ℂ 2 (Ultraspherical.measure lam)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  have hComp : HilbertSchmidtBasis.IsHS
      ((C lam alpha hlam ha).adjoint.comp
        (C lam alpha hlam ha)) :=
    HilbertSchmidtBasis.isHS_comp_left
      (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha)
      (C lam alpha hlam ha).adjoint
  exact hComp b

/-- Both independent Physlib source predicates have genuine witnesses
for the exact same nontruncated positive Gram operator. -/
theorem gram_inPhyslibS1_and_S2
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.IsTraceClass (gram lam alpha hlam ha) ∧
    ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      (gram lam alpha hlam ha) :=
  ⟨gram_isTraceClass lam alpha hlam ha,
   gram_isPhyslibHilbertSchmidt lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_isPhyslibHilbertSchmidt
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_inPhyslibS1_and_S2

end GegenbauerFock.GeneralUltrasphericalFock
