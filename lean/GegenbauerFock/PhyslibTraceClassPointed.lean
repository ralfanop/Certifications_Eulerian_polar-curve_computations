import GegenbauerFock.PhyslibTraceClassScalar

/-!
# V007 — algebraic pointed structure of the Physlib-compatible S₁ carrier

The genuinely CFC-based `ProbabilisticTheory.TraceClass H` already has
scalar closure (proved in `PhyslibTraceClassScalar`). Here we add
the zero and additive-inverse operations and certify the scalar action
laws on the *proof-carrying operator subtype*, without introducing a
hypothetical general addition theorem.

This is a strictly incremental algebraic milestone, NOT yet the full
additive subgroup, normed space, or Banach trace ideal. Generic S₁
addition, norm triangle inequality, and completeness remain open.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The zero bounded operator is a genuine element of the CFC-based
trace-class carrier in any complete complex Hilbert space. -/
instance : Zero (TraceClass H) where
  zero := ⟨0, ProbabilisticTheory.isTraceClass_zero⟩

/-- Negation preserves the actual trace-class membership predicate. -/
instance : Neg (TraceClass H) where
  neg T := ⟨-T.1, ProbabilisticTheory.isTraceClass_neg T.2⟩

@[simp] theorem zero_underlying :
    ((0 : TraceClass H).1) = (0 : H →L[ℂ] H) := rfl

@[simp] theorem neg_underlying (T : TraceClass H) :
    (-T).1 = -T.1 := rfl

/-- Negating a trace-class operator twice gives the same
proof-carrying element (the membership witness is irrelevant). -/
@[simp] theorem neg_neg_element (T : TraceClass H) :
    -(-T) = T := by
  apply Subtype.ext
  change -(-T.1) = T.1
  exact neg_neg T.1

/-- The negative of the zero trace-class operator is zero. -/
@[simp] theorem neg_zero_element :
    -(0 : TraceClass H) = 0 := by
  apply Subtype.ext
  change -(0 : H →L[ℂ] H) = 0
  exact neg_zero

/-- Scalar multiplication is an actual monoid action on the carrier:
its proofs do not depend on the chosen trace-class witnesses. -/
noncomputable instance : MulAction ℂ (TraceClass H) where
  one_smul T := by
    apply Subtype.ext
    change (1 : ℂ) • T.1 = T.1
    exact one_smul ℂ T.1
  mul_smul c d T := by
    apply Subtype.ext
    change (c * d) • T.1 = c • (d • T.1)
    exact mul_smul c d T.1

/-- Zero scalar multiplication sends any trace-class operator to the
distinguished zero trace-class element. -/
@[simp] theorem zero_smul_element (T : TraceClass H) :
    (0 : ℂ) • T = 0 := by
  apply Subtype.ext
  change (0 : ℂ) • T.1 = (0 : H →L[ℂ] H)
  exact zero_smul ℂ T.1

/-- Any scalar multiplication of the zero trace-class operator
remains zero. -/
@[simp] theorem smul_zero_element (c : ℂ) :
    c • (0 : TraceClass H) = 0 := by
  apply Subtype.ext
  change c • (0 : H →L[ℂ] H) = 0
  exact smul_zero c

/-- The CFC-based trace norm of the zero operator-with-proof
is exactly zero in every Hilbert dimension. -/
@[simp] theorem traceNorm_zero_element :
    traceNorm H (0 : TraceClass H) = 0 := by
  unfold traceNorm ProbabilisticTheory.traceNorm
  simp [CFC.abs_zero]

#print axioms ProbabilisticTheory.TraceClass.zero_underlying
#print axioms ProbabilisticTheory.TraceClass.neg_underlying
#print axioms ProbabilisticTheory.TraceClass.neg_neg_element
#print axioms ProbabilisticTheory.TraceClass.neg_zero_element
#print axioms ProbabilisticTheory.TraceClass.zero_smul_element
#print axioms ProbabilisticTheory.TraceClass.smul_zero_element
#print axioms ProbabilisticTheory.TraceClass.traceNorm_zero_element

end ProbabilisticTheory.TraceClass
