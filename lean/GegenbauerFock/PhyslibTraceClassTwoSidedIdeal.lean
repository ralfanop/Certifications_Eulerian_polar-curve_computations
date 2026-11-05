import GegenbauerFock.PhyslibGeneralHSProductTraceClass
import GegenbauerFock.PhyslibTraceClassHSFactorization

/-!
# V007 — the full two-sided CFC trace-class operator ideal

Once both exact Hilbert--Schmidt product directions are established,
the source-compatible trace-class predicate is stable under arbitrary
bounded left and right multiplication, without any positivity,
finite-rank, or particular ultraspherical kernel hypothesis.

This is the *membership* version of the two-sided Schatten S1 ideal
property; the sharp trace-norm estimate and completeness remain separate
formalization tasks. No extra axioms or `sorry` are introduced.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For any CFC-trace-class T and bounded A, B, the actual
two-sided product A*T*B belongs to the source-compatible S1 class. -/
theorem isTraceClass_twoSided
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (A B : H →L[ℂ] H) :
    IsTraceClass (A * T * B) := by
  obtain ⟨R, S, hR, hS, hRS⟩ := traceClass_exists_HS_mul_HS T hT
  have hAR : HilbertSchmidt.IsHilbertSchmidt (A * R) := by
    change HilbertSchmidt.IsHilbertSchmidt (A.comp R)
    exact HilbertSchmidt.isHilbertSchmidt_comp_left R hR A
  have hSB : HilbertSchmidt.IsHilbertSchmidt (S * B) := by
    change HilbertSchmidt.IsHilbertSchmidt (S.comp B)
    exact HilbertSchmidt.isHilbertSchmidt_comp_right S hS B
  have hprod : IsTraceClass ((A * R) * (S * B)) :=
    isTraceClass_mul_of_twoHilbertSchmidt (A * R) (S * B) hAR hSB
  have heq : (A * R) * (S * B) = A * T * B := by
    calc
      (A * R) * (S * B) = A * (R * S) * B := by
        simp only [mul_assoc]
      _ = A * T * B := by rw [hRS]
  rw [← heq]
  exact hprod

/-- Left bounded multiplication preserves the full nonpositive S1
predicate, without a trace-norm estimate. -/
theorem isTraceClass_mul_left
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (A : H →L[ℂ] H) :
    IsTraceClass (A * T) := by
  simpa only [mul_one] using isTraceClass_twoSided T hT A 1

/-- Right bounded multiplication preserves the full nonpositive S1
predicate, without a trace-norm estimate. -/
theorem isTraceClass_mul_right
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (B : H →L[ℂ] H) :
    IsTraceClass (T * B) := by
  simpa only [one_mul] using isTraceClass_twoSided T hT 1 B

/-- Adjoint closure for the *entire* nonpositive CFC-based S1 class.
A trace-class operator factors as R*S with R,S Hilbert--Schmidt;
taking adjoints reverses the two genuine HS factors. -/
theorem isTraceClass_adjoint
    (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    IsTraceClass T.adjoint := by
  obtain ⟨R, S, hR, hS, hRS⟩ := traceClass_exists_HS_mul_HS T hT
  have hSstar : HilbertSchmidt.IsHilbertSchmidt S.adjoint :=
    HilbertSchmidt.isHilbertSchmidt_adjoint S hS
  have hRstar : HilbertSchmidt.IsHilbertSchmidt R.adjoint :=
    HilbertSchmidt.isHilbertSchmidt_adjoint R hR
  have hprod : IsTraceClass (S.adjoint * R.adjoint) :=
    isTraceClass_mul_of_twoHilbertSchmidt
      S.adjoint R.adjoint hSstar hRstar
  have heq : T.adjoint = S.adjoint * R.adjoint := by
    rw [← hRS]
    change (R.comp S).adjoint = S.adjoint.comp R.adjoint
    exact ContinuousLinearMap.adjoint_comp R S
  rw [heq]
  exact hprod

namespace TraceClass

/-- The actual subtype of nonpositive trace-class operators
is preserved by taking the bounded Hilbert-space adjoint. -/
noncomputable def adjoint (T : TraceClass H) : TraceClass H :=
  ⟨T.1.adjoint, isTraceClass_adjoint T.1 T.2⟩

@[simp] theorem adjoint_operator (T : TraceClass H) :
    (adjoint T).1 = T.1.adjoint := rfl

/-- The proof-carrying adjoint involution holds without
assuming any trace-norm or Banach-space structure. -/
@[simp] theorem adjoint_adjoint (T : TraceClass H) :
    adjoint (adjoint T) = T := by
  apply Subtype.ext
  exact ContinuousLinearMap.adjoint_adjoint T.1

end TraceClass

#print axioms ProbabilisticTheory.isTraceClass_adjoint
#print axioms ProbabilisticTheory.TraceClass.adjoint_operator
#print axioms ProbabilisticTheory.TraceClass.adjoint_adjoint

#print axioms ProbabilisticTheory.isTraceClass_twoSided
#print axioms ProbabilisticTheory.isTraceClass_mul_left
#print axioms ProbabilisticTheory.isTraceClass_mul_right

end ProbabilisticTheory
