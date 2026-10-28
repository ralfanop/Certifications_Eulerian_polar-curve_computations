import GegenbauerFock.PhyslibTraceClassAdditionFromHS
import GegenbauerFock.PhyslibTraceClassScalar

/-!
# V007 — abstract additive subgroup of all CFC trace-class endomorphisms

The general nonpositive addition theorem from the polar/HS proof,
the already-certified scalar-closure negation theorem, and zero
membership together define a genuine AddSubgroup of bounded complex
Hilbert-space endomorphisms. This gives an honest additive group,
with no hand-written group axioms or placeholder typeclasses.

The subgroup carries the same underlying predicate as
ProbabilisticTheory.TraceClass H. Norm and completeness are NOT
obtained by this purely algebraic construction.
-/

noncomputable section

namespace ProbabilisticTheory

variable (H : Type*)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual unrestricted Physlib-compatible Schatten S₁
operators form an additive subgroup of bounded complex endomorphisms. -/
def traceClassAddSubgroup : AddSubgroup (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  zero_mem' := isTraceClass_zero
  add_mem' := by
    intro T V hT hV
    exact isTraceClass_add_via_polarHS hT hV
  neg_mem' := by
    intro T hT
    exact isTraceClass_neg hT

/-- Membership in the additive subgroup is definitionally the genuine
functional-calculus absolute trace-class condition. -/
@[simp] theorem mem_traceClassAddSubgroup (T : H →L[ℂ] H) :
    T ∈ traceClassAddSubgroup H ↔ IsTraceClass T := Iff.rfl

/-- Finite sums of arbitrary nonpositive S₁ operators remain in S₁,
as an immediate consequence of their additive subgroup structure. -/
theorem isTraceClass_finset_sum
    {ι : Type*} (s : Finset ι)
    (T : ι → H →L[ℂ] H)
    (hT : ∀ i ∈ s, IsTraceClass (T i)) :
    IsTraceClass (∑ i ∈ s, T i) := by
  change (∑ i ∈ s, T i) ∈ traceClassAddSubgroup H
  exact AddSubgroup.sum_mem (traceClassAddSubgroup H) s hT

#print axioms ProbabilisticTheory.mem_traceClassAddSubgroup
#print axioms ProbabilisticTheory.isTraceClass_finset_sum

end ProbabilisticTheory
