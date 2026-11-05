import GegenbauerFock.PhyslibTraceClassSandwichSubtype
import GegenbauerFock.PhyslibTraceClassIdealNormSharp
import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — bounded, complex-linear two-sided Schatten S₁ action

On any complete complex Hilbert space, the *actual* CFC-trace-normed
Physlib-compatible trace-class subtype carries a continuous complex
linear map T ↦ A*T*B for every pair of bounded operators A and B.
Its operator norm is bounded by ‖A‖*‖B‖ with the sharp constant 1.

The construction does not require S₁ Banach completeness, and does
not identify its norm with the ambient B(H) operator norm.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine CFC trace-class sandwich is a complex-linear map
in the trace-class variable, without a positivity hypothesis. -/
noncomputable def sandwichLinear (A B : H →L[ℂ] H) :
    TraceClass H →ₗ[ℂ] TraceClass H where
  toFun T := sandwich T A B
  map_add' T V := by
    apply Subtype.ext
    change A * (T.1 + V.1) * B =
      (A * T.1 * B) + (A * V.1 * B)
    simp only [mul_add, add_mul]
  map_smul' c T := by
    apply Subtype.ext
    change A * (c • T.1) * B = c • (A * T.1 * B)
    simp only [mul_smul_comm, smul_mul_assoc]

@[simp] theorem sandwichLinear_apply
    (A B : H →L[ℂ] H) (T : TraceClass H) :
    sandwichLinear A B T = sandwich T A B := rfl

/-- The sharp bilateral CFC S₁ estimate makes the algebraic action
continuous for the *actual* trace norm, without completeness. -/
noncomputable def sandwichContinuous (A B : H →L[ℂ] H) :
    TraceClass H →L[ℂ] TraceClass H :=
  (sandwichLinear A B).mkContinuous (‖A‖ * ‖B‖) (by
    intro T
    change ProbabilisticTheory.traceNorm
        (A * T.1 * B)
        (ProbabilisticTheory.isTraceClass_twoSided T.1 T.2 A B) ≤
      (‖A‖ * ‖B‖) * ProbabilisticTheory.traceNorm T.1 T.2
    exact ProbabilisticTheory.traceNorm_twoSided_le T.1 A B T.2)

@[simp] theorem sandwichContinuous_apply
    (A B : H →L[ℂ] H) (T : TraceClass H) :
    sandwichContinuous A B T = sandwich T A B := rfl

/-- Operator norm estimate on B(S₁), not merely on B(H). -/
theorem sandwichContinuous_norm_le
    (A B : H →L[ℂ] H) :
    ‖sandwichContinuous A B‖ ≤ ‖A‖ * ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg A) (norm_nonneg B))
  intro T
  change ProbabilisticTheory.traceNorm
      (A * T.1 * B)
      (ProbabilisticTheory.isTraceClass_twoSided T.1 T.2 A B) ≤
    (‖A‖ * ‖B‖) * ProbabilisticTheory.traceNorm T.1 T.2
  exact ProbabilisticTheory.traceNorm_twoSided_le T.1 A B T.2

/-- The actual bounded action by the identity operators is the
identity on the proof-carrying trace class. -/
theorem sandwichContinuous_one_one (T : TraceClass H) :
    sandwichContinuous (1 : H →L[ℂ] H) 1 T = T := by
  rw [sandwichContinuous_apply, sandwich_one_one]

#print axioms ProbabilisticTheory.TraceClass.sandwichLinear_apply
#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_apply
#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_norm_le
#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_one_one

end ProbabilisticTheory.TraceClass
