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

#print axioms ProbabilisticTheory.isTraceClass_twoSided
#print axioms ProbabilisticTheory.isTraceClass_mul_left
#print axioms ProbabilisticTheory.isTraceClass_mul_right

end ProbabilisticTheory
