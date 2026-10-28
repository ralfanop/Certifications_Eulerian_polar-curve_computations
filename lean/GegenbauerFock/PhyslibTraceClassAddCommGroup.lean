import GegenbauerFock.PhyslibTraceClassAdditiveCarrier

/-!
# V007 — additive abelian group structure of the actual S₁ carrier

The CFC-based Physlib-compatible trace-class subtype has already
been equipped with zero, negation and arbitrary addition of operators
(using the two-Hilbert–Schmidt factorization). This module packages
those operations as a genuine `AddCommGroup`.

The operation is the actual sum of bounded endomorphisms, with
proof-irrelevant trace-class witnesses. No finite-dimensional
assumption, positivity restriction or unproved norm inequalities.
This does NOT assert the trace-norm triangle inequality or completeness.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic S₁ is an additive abelian group, before introducing
any yet-unproved trace-normed/Banach-space structure. -/
noncomputable instance : AddCommGroup (TraceClass H) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := fun T V => T + (-V)
  add_assoc := add_assoc_element
  add_comm := add_comm_element
  zero_add := zero_add_element
  add_zero := add_zero_element
  neg_add_cancel := neg_add_element
  sub_eq_add_neg := by
    intro T V
    rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The group subtraction is precisely subtraction of the
underlying bounded Hilbert-space endomorphisms. -/
@[simp] theorem sub_operator (T V : TraceClass H) :
    ((T - V : TraceClass H).1) = T.1 - V.1 := by
  change T.1 + -V.1 = T.1 - V.1
  exact (sub_eq_add_neg T.1 V.1).symm

/-- The canonical forgetful map is injective: distinct trace-class
elements cannot represent the same bounded operator. -/
theorem operator_injective :
    Function.Injective (operator H) := by
  intro T V h
  exact Subtype.ext h

#print axioms ProbabilisticTheory.TraceClass.sub_operator
#print axioms ProbabilisticTheory.TraceClass.operator_injective

end ProbabilisticTheory.TraceClass
