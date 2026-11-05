import GegenbauerFock.PhyslibTraceClassGeneralAdd

/-!
# V007 — arbitrary finite S₁ linear combinations without positivity

Consequences of the unrestricted trace-class addition theorem, distinct
from the earlier positive cone. This is a candidate pending the exact-SHA
CI: it introduces no axioms and does not assert Banach completeness.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The difference of two arbitrary (possibly non-self-adjoint) complex
trace-class operators belongs to the CFC-absolute trace class. -/
theorem isTraceClass_sub_general
    (T S : H →L[ℂ] H)
    (hT : IsTraceClass T) (hS : IsTraceClass S) :
    IsTraceClass (T - S) := by
  have h := isTraceClass_add_general T (-S) hT (isTraceClass_neg hS)
  simpa only [sub_eq_add_neg] using h

/-- Any finite sum of arbitrary complex trace-class endomorphisms is
trace class; neither positivity nor a common-basis premise is needed. -/
theorem isTraceClass_finset_sum_general
    {ι : Type*} (s : Finset ι)
    (T : ι → H →L[ℂ] H)
    (hT : ∀ i ∈ s, IsTraceClass (T i)) :
    IsTraceClass (∑ i ∈ s, T i) := by
  classical
  revert hT
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using (isTraceClass_zero (H := H))
  | @insert a s ha ih =>
      intro hT
      rw [Finset.sum_insert ha]
      exact isTraceClass_add_general (T a) (∑ i ∈ s, T i)
        (hT a (Finset.mem_insert_self a s))
        (ih (fun i hi => hT i (Finset.mem_insert_of_mem hi)))

#print axioms ProbabilisticTheory.isTraceClass_sub_general
#print axioms ProbabilisticTheory.isTraceClass_finset_sum_general

end ProbabilisticTheory
