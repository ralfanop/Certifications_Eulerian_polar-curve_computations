import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal
import GegenbauerFock.PhyslibTraceClassSubtype

/-!
# V007 — proof-carrying two-sided actions on the CFC trace-class subtype

The general (possibly non-self-adjoint) trace-class two-sided ideal
membership theorem can be lifted to the concrete operator-with-proof
carrier `ProbabilisticTheory.TraceClass H`.  The resulting sandwich
operation is compatible with the underlying bounded operators and
associative under composition of the two bounded multipliers.

This is an algebraic, not yet normed, trace-class API.  It makes no
claim about the quantitative trace-norm ideal bound, full additive
closure, the triangle inequality, or Banach completeness.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The true CFC-based trace-class subtype is preserved by arbitrary
bounded left and right multiplication, with no positivity assumption. -/
noncomputable def sandwich (T : TraceClass H)
    (A B : H →L[ℂ] H) : TraceClass H :=
  ⟨A * T.1 * B,
    ProbabilisticTheory.isTraceClass_twoSided T.1 T.2 A B⟩

@[simp] theorem sandwich_operator (T : TraceClass H)
    (A B : H →L[ℂ] H) :
    (sandwich T A B).1 = A * T.1 * B := rfl

@[simp] theorem sandwich_one_one (T : TraceClass H) :
    sandwich T 1 1 = T := by
  apply Subtype.ext
  change (1 : H →L[ℂ] H) * T.1 * 1 = T.1
  simp

/-- Composition of bounded multipliers induces the expected reverse
order on the right factor, on the actual witness-carrying type. -/
theorem sandwich_compose (T : TraceClass H)
    (A B C D : H →L[ℂ] H) :
    sandwich (sandwich T A B) C D =
      sandwich T (C * A) (B * D) := by
  apply Subtype.ext
  change C * (A * T.1 * B) * D =
    (C * A) * T.1 * (B * D)
  simp only [mul_assoc]

/-- The same typed construction for bounded adjoint conjugation,
without positivity or self-adjointness of the trace-class input. -/
noncomputable def conjugate (T : TraceClass H)
    (B : H →L[ℂ] H) : TraceClass H :=
  sandwich T B.adjoint B

@[simp] theorem conjugate_operator (T : TraceClass H)
    (B : H →L[ℂ] H) :
    (conjugate T B).1 = B.adjoint * T.1 * B := rfl

@[simp] theorem conjugate_one (T : TraceClass H) :
    conjugate T 1 = T := by
  unfold conjugate
  simpa only [ContinuousLinearMap.adjoint_one] using (sandwich_one_one T)

#print axioms ProbabilisticTheory.TraceClass.sandwich_operator
#print axioms ProbabilisticTheory.TraceClass.sandwich_one_one
#print axioms ProbabilisticTheory.TraceClass.sandwich_compose
#print axioms ProbabilisticTheory.TraceClass.conjugate_operator
#print axioms ProbabilisticTheory.TraceClass.conjugate_one

end ProbabilisticTheory.TraceClass
