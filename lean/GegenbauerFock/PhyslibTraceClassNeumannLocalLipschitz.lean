import GegenbauerFock.PhyslibTraceClassNeumannTraceNormStability
import GegenbauerFock.PhyslibTraceClassNeumannInverseNormBound

/-!
# V007 — explicit local trace-norm Lipschitz modulus for Neumann corrections

Let T,U be arbitrary (not necessarily positive or commuting) CFC
Schatten-S₁ operators, each with genuine trace norm below one.
The exact two-point resolvent identity together with the sharp CFC
S₁ ideal estimate yields a quantitative bound on the difference
of the true nonunital Neumann corrections, with explicit scalar
coefficients depending separately on ‖T‖₁ and ‖U‖₁.

The unit here lives in the ambient bounded-operator algebra B(H);
we make no assertion that the identity operator lies in S₁(H).
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The noncommutative Neumann correction is locally Lipschitz in the
*actual CFC Schatten trace norm*, with an explicit pairwise modulus.
No normality, positivity, or finite-dimensional hypotheses. -/
theorem neumannCorrection_localLipschitz_traceNorm
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    traceNorm H (neumannCorrection T - neumannCorrection U) ≤
      ((‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖)) *
       (‖(1 : H →L[ℂ] H)‖ + ‖U‖ / (1 - ‖U‖))) *
      traceNorm H (T - U) := by
  have hAT := neumann_ambient_inverse_norm_le T hT
  have hBU := neumann_ambient_inverse_norm_le U hU
  have hATnonneg :
      0 ≤ ‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖) :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (norm_nonneg _) (le_of_lt (sub_pos.mpr hT)))
  have hmul :
      (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
        ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖) ≤
      (‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖)) *
        (‖(1 : H →L[ℂ] H)‖ + ‖U‖ / (1 - ‖U‖)) :=
    mul_le_mul hAT hBU (norm_nonneg _) hATnonneg
  have htrace : 0 ≤ traceNorm H (T - U) := by
    change 0 ≤ ‖T - U‖
    exact norm_nonneg _
  calc
    traceNorm H (neumannCorrection T - neumannCorrection U) ≤
        (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
          ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖) *
          traceNorm H (T - U) :=
      neumann_resolvent_traceNorm_stability T U hT hU
    _ ≤ ((‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖)) *
          (‖(1 : H →L[ℂ] H)‖ + ‖U‖ / (1 - ‖U‖))) *
          traceNorm H (T - U) :=
      mul_le_mul_of_nonneg_right hmul htrace

#print axioms ProbabilisticTheory.TraceClass.neumannCorrection_localLipschitz_traceNorm

end ProbabilisticTheory.TraceClass
