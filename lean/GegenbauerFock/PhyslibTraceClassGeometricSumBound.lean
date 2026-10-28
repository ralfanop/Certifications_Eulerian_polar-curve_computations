import GegenbauerFock.PhyslibTraceClassGeometricTail

/-!
# V007 — full nonunital geometric sum has a sharp CFC S₁ majorant

The already certified geometric truncation bound controls the norm
of the full nonunital resolvent correction. Taking N = 0 proves
the sharp scalar majorant ‖T‖₁/(1-‖T‖₁) for arbitrary nonnormal
trace-class T, in both the actual CFC Schatten-S₁ trace norm and
the ambient bounded-operator norm. No identity operator in S₁ is
assumed or used.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Explicit norm control of the entire nonunital geometric sum
in the genuine CFC Schatten trace norm, with no positivity or
commutativity assumptions. -/
theorem positivePowers_total_traceNorm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    traceNorm H (∑' n : ℕ, positivePower T n) ≤
      ‖T‖ / (1 - ‖T‖) := by
  have h := positivePowers_traceNorm_error_le_geometric T hsmall 0
  simpa only [Finset.range_zero, Finset.sum_empty, sub_zero,
    zero_add, pow_one] using h

/-- The same coefficient-one majorant bounds the full geometric
correction in the ambient operator norm. -/
theorem positivePowers_total_operatorNorm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    ‖((∑' n : ℕ, positivePower T n) : TraceClass H).1‖ ≤
      ‖T‖ / (1 - ‖T‖) := by
  have h := positivePowers_operatorNorm_error_le_geometric T hsmall 0
  simpa only [Finset.range_zero, Finset.sum_empty, sub_zero,
    zero_add, pow_one] using h

#print axioms ProbabilisticTheory.TraceClass.positivePowers_total_traceNorm_le
#print axioms ProbabilisticTheory.TraceClass.positivePowers_total_operatorNorm_le

end ProbabilisticTheory.TraceClass
