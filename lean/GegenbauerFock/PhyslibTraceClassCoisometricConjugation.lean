import GegenbauerFock.PhyslibTraceClassGeneralConjugationBound

/-!
# V007 — exact CFC trace-norm invariance under coisometric conjugation

The genuine Schatten-S₁ trace norm is invariant under
T ↦ U† T U for any bounded Hilbert-space coisometry U.

The assumptions U*U† = 1 and ‖U‖ ≤ 1 include every unitary
operator but are more general: the operator U need not be injective.
The reverse inequality follows by conjugating back with U†,
and both directions use the already kernel-certified *nonpositive*
sharp CFC S₁ conjugation bound.

Unlike the earlier positive-cone trace norm identity, this theorem
holds for any possibly nonnormal and nonselfadjoint T ∈ S₁.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugating a trace-class operator by a coisometry U and then
by its adjoint recovers the original operator on the nose. -/
theorem coisometric_conjugate_inverse_v007
    (T : TraceClass H) (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1) :
    conjugate (conjugate T U) U.adjoint = T := by
  apply Subtype.ext
  calc
    (conjugate (conjugate T U) U.adjoint).1 =
        U * (U.adjoint * T.1 * U) * U.adjoint := by
          simp only [conjugate_operator, ContinuousLinearMap.adjoint_adjoint]
    _ = (U * U.adjoint) * T.1 * (U * U.adjoint) := by
      simp only [mul_assoc]
    _ = T.1 := by rw [hUUstar]; simp

/-- The *actual* CFC Schatten trace norm, not the bounded-operator
norm, is exactly invariant under coisometric conjugation. -/
theorem coisometric_conjugate_traceNorm_eq_v007
    (T : TraceClass H) (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ)) :
    traceNorm H (conjugate T U) = traceNorm H T := by
  have hAdjNorm : ‖U.adjoint‖ ≤ (1 : ℝ) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    simpa only [norm_star] using hUnorm
  have hforward :
      traceNorm H (conjugate T U) ≤ traceNorm H T :=
    conjugate_traceNorm_le_general_contraction_v007 T U hUnorm
  have hback :
      traceNorm H T ≤ traceNorm H (conjugate T U) := by
    have h :=
      conjugate_traceNorm_le_general_contraction_v007
        (conjugate T U) U.adjoint hAdjNorm
    rw [coisometric_conjugate_inverse_v007 T U hUUstar] at h
    exact h
  exact le_antisymm hforward hback

#print axioms ProbabilisticTheory.TraceClass.coisometric_conjugate_inverse_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_conjugate_traceNorm_eq_v007

end ProbabilisticTheory.TraceClass
