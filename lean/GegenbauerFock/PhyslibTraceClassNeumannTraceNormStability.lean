import GegenbauerFock.PhyslibTraceClassNeumannResolventIdentity
import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — true Schatten-S₁ trace-norm stability of Neumann corrections

For any two CFC Schatten-S₁ contractions T,U, the ambient two-point
resolvent identity is also an identity of the true trace-class elements.
The sharp two-sided ideal inequality then gives a trace-norm (rather
than merely operator-norm) perturbation bound.

No commutativity, positivity, shared eigenvectors, or finite-dimensional
assumptions. In particular, the ambient identity operator is never
asserted to belong to S₁.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient two-point identity lifts to equality of genuine CFC
trace-class operators, with the actual bilateral ideal operation. -/
theorem neumann_resolvent_sandwich_eq
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    neumannCorrection T - neumannCorrection U =
      sandwich (T - U)
        ((1 : H →L[ℂ] H) + (neumannCorrection T).1)
        ((1 : H →L[ℂ] H) + (neumannCorrection U).1) := by
  apply Subtype.ext
  change (neumannCorrection T).1 - (neumannCorrection U).1 =
    ((1 : H →L[ℂ] H) + (neumannCorrection T).1) *
    (T.1 - U.1) *
    ((1 : H →L[ℂ] H) + (neumannCorrection U).1)
  exact neumann_ambient_resolvent_identity T U hT hU

/-- Sharp coefficient-one bilateral ideal control of the Neumann
correction difference in the *actual CFC trace norm*. -/
theorem neumann_resolvent_traceNorm_stability
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    traceNorm H (neumannCorrection T - neumannCorrection U) ≤
      (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
        ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖) *
      traceNorm H (T - U) := by
  let A : H →L[ℂ] H := 1 + (neumannCorrection T).1
  let B : H →L[ℂ] H := 1 + (neumannCorrection U).1
  have hid : neumannCorrection T - neumannCorrection U =
      sandwich (T - U) A B := by
    simpa only [A, B] using neumann_resolvent_sandwich_eq T U hT hU
  have hbound : ‖sandwich (T - U) A B‖ ≤
      (‖A‖ * ‖B‖) * ‖T - U‖ := by
    calc
      ‖sandwich (T - U) A B‖ =
        ‖sandwichContinuous A B (T - U)‖ := rfl
      _ ≤ ‖sandwichContinuous A B‖ * ‖T - U‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A‖ * ‖B‖) * ‖T - U‖ :=
        mul_le_mul_of_nonneg_right (sandwichContinuous_norm_le A B) (norm_nonneg _)
  rw [hid]
  simpa only [norm_eq_genuineTraceNorm, A, B] using hbound

#print axioms ProbabilisticTheory.TraceClass.neumann_resolvent_sandwich_eq
#print axioms ProbabilisticTheory.TraceClass.neumann_resolvent_traceNorm_stability

end ProbabilisticTheory.TraceClass
