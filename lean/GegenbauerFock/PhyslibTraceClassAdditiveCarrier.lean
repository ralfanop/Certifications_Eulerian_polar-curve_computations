import GegenbauerFock.PhyslibTraceClassAdditionFromHS
import GegenbauerFock.PhyslibTraceClassPointed

/-!
# V007 — genuine additive operations on the Physlib-compatible S₁ carrier

Unlike the earlier pointed subtype, this file constructs actual addition
of arbitrary trace-class operators, using the CFC/Hilbert–Schmidt
closure theorem rather than positivity or a finite-dimensional proxy.
The identities below are exact identities of the underlying bounded
operators, with proof-irrelevant membership witnesses.

This module does not assume a trace-norm triangle inequality or
a completed normed-group structure; those remain independent goals.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Addition of arbitrary, possibly non-self-adjoint, CFC trace-class
endomorphisms, carrying an actual membership proof. -/
noncomputable instance : Add (TraceClass H) where
  add T V := ⟨T.1 + V.1,
    ProbabilisticTheory.isTraceClass_add_via_polarHS T.2 V.2⟩

@[simp] theorem add_operator (T V : TraceClass H) :
    ((T + V : TraceClass H).1) = T.1 + V.1 := rfl

/-- The trace-class subtype inherits associativity from bounded maps. -/
theorem add_assoc_element (T V W : TraceClass H) :
    (T + V) + W = T + (V + W) := by
  apply Subtype.ext
  change (T.1 + V.1) + W.1 = T.1 + (V.1 + W.1)
  exact add_assoc _ _ _

theorem add_comm_element (T V : TraceClass H) :
    T + V = V + T := by
  apply Subtype.ext
  change T.1 + V.1 = V.1 + T.1
  exact add_comm _ _

theorem zero_add_element (T : TraceClass H) :
    0 + T = T := by
  apply Subtype.ext
  change (0 : H →L[ℂ] H) + T.1 = T.1
  exact zero_add _

theorem add_zero_element (T : TraceClass H) :
    T + 0 = T := by
  apply Subtype.ext
  change T.1 + (0 : H →L[ℂ] H) = T.1
  exact add_zero _

theorem add_neg_element (T : TraceClass H) :
    T + (-T) = 0 := by
  apply Subtype.ext
  change T.1 + (-T.1) = (0 : H →L[ℂ] H)
  exact add_neg_cancel T.1

theorem neg_add_element (T : TraceClass H) :
    (-T) + T = 0 := by
  apply Subtype.ext
  change -T.1 + T.1 = (0 : H →L[ℂ] H)
  exact neg_add_cancel T.1

/-- Scalar multiplication distributes over actual trace-class
addition; no trace-norm inequality is invoked. -/
theorem smul_add_element (c : ℂ) (T V : TraceClass H) :
    c • (T + V) = c • T + c • V := by
  apply Subtype.ext
  change c • (T.1 + V.1) = c • T.1 + c • V.1
  exact smul_add c T.1 V.1

/-- Additivity in the complex scalar variable. -/
theorem add_smul_element (c d : ℂ) (T : TraceClass H) :
    (c + d) • T = c • T + d • T := by
  apply Subtype.ext
  change (c + d) • T.1 = c • T.1 + d • T.1
  exact add_smul c d T.1

#print axioms ProbabilisticTheory.TraceClass.add_operator
#print axioms ProbabilisticTheory.TraceClass.add_assoc_element
#print axioms ProbabilisticTheory.TraceClass.add_comm_element
#print axioms ProbabilisticTheory.TraceClass.zero_add_element
#print axioms ProbabilisticTheory.TraceClass.add_zero_element
#print axioms ProbabilisticTheory.TraceClass.add_neg_element
#print axioms ProbabilisticTheory.TraceClass.neg_add_element
#print axioms ProbabilisticTheory.TraceClass.smul_add_element
#print axioms ProbabilisticTheory.TraceClass.add_smul_element

end ProbabilisticTheory.TraceClass
