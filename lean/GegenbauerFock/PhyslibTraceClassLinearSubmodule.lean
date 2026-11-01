import GegenbauerFock.PhyslibTraceClassAdditionFromHS
import GegenbauerFock.PhyslibTraceClassScalar

/-!
# V007 — genuine complex-linear submodule of CFC trace-class operators

The full source-compatible Physlib CFC-absolute S₁ predicate is a
complex linear submodule of all bounded complex Hilbert endomorphisms.
The proof uses the previously kernel-checked arbitrary (nonpositive)
trace-class addition theorem and actual scalar-multiplication closure,
not an assumed trace-norm triangle inequality.

Consequently arbitrary FINITE complex-linear combinations of S₁ maps
remain S₁. The construction is independent of the ultraspherical
example and of the dimension of H.

No Banach norm, continuity, operator norm versus trace norm
equivalence, or completeness is asserted here.
-/

noncomputable section

namespace ProbabilisticTheory

variable (H : Type*)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every CFC-absolute trace-class operator belongs to an actual
complex linear submodule of the bounded Hilbert endomorphisms. -/
noncomputable def traceClassLinearSubmodule : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  zero_mem' := isTraceClass_zero
  add_mem' := by
    intro T V hT hV
    exact isTraceClass_add_via_polarHS hT hV
  smul_mem' := by
    intro c T hT
    exact isTraceClass_smul c hT

@[simp] theorem mem_traceClassLinearSubmodule (T : H →L[ℂ] H) :
    T ∈ traceClassLinearSubmodule H ↔ IsTraceClass T := Iff.rfl

/-- Closure under arbitrary FINITE complex-linear combinations;
no positivity or common Hilbert-basis hypothesis on the summands. -/
theorem isTraceClass_finset_linearCombination
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (T : ι → H →L[ℂ] H)
    (hT : ∀ i ∈ s, IsTraceClass (T i)) :
    IsTraceClass (∑ i ∈ s, c i • T i) := by
  classical
  revert hT
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using
        (isTraceClass_zero (H := H))
  | @insert i s hi ih =>
      intro hT
      rw [Finset.sum_insert hi]
      exact isTraceClass_add_via_polarHS
        (isTraceClass_smul (c i) (hT i (Finset.mem_insert_self i s)))
        (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

#print axioms ProbabilisticTheory.mem_traceClassLinearSubmodule
#print axioms ProbabilisticTheory.isTraceClass_finset_linearCombination

end ProbabilisticTheory
