import GegenbauerFock.PhyslibMixedGramAlgebra
import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal

/-!
# V007 — concrete mixed Gram membership in the source-compatible Schatten S₁ class

This new module applies the independently formulated general nonpositive
two-sided trace-ideal theorem to the actual Gegenbauer–Fock Gram.
Unlike the positive conjugation result, B and D are arbitrary and
independent. No positivity, commutativity, or finite rank is assumed.

The norm bound is a separate obligation: membership here MUST NOT
be represented as the sharp Hölder trace-norm inequality. The parent
generic two-sided theorem and this new source require their own exact-SHA
Lean build and axiom audit before certification.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Arbitrary bounded left and right multiplication of the genuine
ultraspherical Gram is source-compatible Physlib trace class. -/
theorem gram_twoSided_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.IsTraceClass
      (A * (gram lam alpha hlam ha) * B) :=
  ProbabilisticTheory.isTraceClass_twoSided
    (gram lam alpha hlam ha)
    (gram_isTraceClass lam alpha hlam ha) A B

/-- The *off-diagonal* Gram B†GD belongs to actual CFC trace class
even when B and D are unrelated or noncommuting. -/
theorem gramMixed_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.IsTraceClass
      (gramMixed lam alpha hlam ha B D) := by
  have h := gram_twoSided_isTraceClass
    lam alpha hlam ha B.adjoint D
  have heq :
      gramMixed lam alpha hlam ha B D =
        B.adjoint * (gram lam alpha hlam ha) * D := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [heq]
  exact h

/-- The mixed Gram as an actual proof-carrying trace-class element. -/
noncomputable def gramMixedTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.TraceClass
      (Lp ℂ 2 (Ultraspherical.measure lam)) :=
  ProbabilisticTheory.TraceClass.ofOperator _
    (gramMixed lam alpha hlam ha B D)
    (gramMixed_isTraceClass lam alpha hlam ha B D)

@[simp] theorem gramMixedTraceClass_operator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.TraceClass.operator _
      (gramMixedTraceClass lam alpha hlam ha B D) =
        gramMixed lam alpha hlam ha B D := rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_twoSided_isTraceClass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_isTraceClass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixedTraceClass_operator

end GegenbauerFock.GeneralUltrasphericalFock
