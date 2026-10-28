import GegenbauerFock.PhyslibTraceClassNeumannGeometricBridge
import GegenbauerFock.PhyslibTraceClassNeumannAmbientInverse
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding

/-!
# V007 — quantitative bounds for the genuine nonunital Neumann correction

The certified S₁ geometric bound and the exact equality between Mathlib
iterated Neumann products and genuine CFC positive powers yield estimates
for the *same* trace-class correction used in the certified ambient inverse.

No unital structure is introduced on S₁(H): the identity belongs only to
the ambient algebra B(H) of bounded complex-linear endomorphisms.
All estimates hold for nonnormal, nonpositive and noncommuting inputs.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact trace norm of the nonunital resolvent correction is bounded
by the scalar geometric majorant for every strict S₁ contraction. -/
theorem neumannCorrection_traceNorm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    traceNorm H (neumannCorrection T) ≤
      ‖T‖ / (1 - ‖T‖) := by
  exact neumann_tsum_traceNorm_le T hsmall

/-- The very same correction obeys an ambient operator-norm bound,
because the true Schatten trace norm dominates the operator norm. -/
theorem neumannCorrection_operatorNorm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    ‖(neumannCorrection T).1‖ ≤ ‖T‖ / (1 - ‖T‖) := by
  calc
    ‖(neumannCorrection T).1‖ ≤ ‖neumannCorrection T‖ :=
      operator_norm_le_trace_norm _
    _ = traceNorm H (neumannCorrection T) :=
      norm_eq_genuineTraceNorm _
    _ ≤ ‖T‖ / (1 - ‖T‖) :=
      neumannCorrection_traceNorm_le T hsmall

/-- The explicit bounded-operator inverse of I-T has norm controlled
by the ambient identity plus the exact CFC trace-norm geometric tail. -/
theorem neumann_ambient_inverse_norm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    ‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ ≤
      ‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖) := by
  calc
    ‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ ≤
      ‖(1 : H →L[ℂ] H)‖ + ‖(neumannCorrection T).1‖ :=
        norm_add_le _ _
    _ ≤ ‖(1 : H →L[ℂ] H)‖ + ‖T‖ / (1 - ‖T‖) :=
      add_le_add_left (neumannCorrection_operatorNorm_le T hsmall) _

/-- The correction itself is exactly the difference between the
ambient Neumann inverse and the ambient identity, with an explicit bound. -/
theorem neumann_ambient_inverse_deviation_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    ‖((1 : H →L[ℂ] H) + (neumannCorrection T).1) - 1‖ ≤
      ‖T‖ / (1 - ‖T‖) := by
  simpa only [add_sub_cancel_left] using
    (neumannCorrection_operatorNorm_le T hsmall)

#print axioms ProbabilisticTheory.TraceClass.neumannCorrection_traceNorm_le
#print axioms ProbabilisticTheory.TraceClass.neumannCorrection_operatorNorm_le
#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_inverse_norm_le
#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_inverse_deviation_le

end ProbabilisticTheory.TraceClass
