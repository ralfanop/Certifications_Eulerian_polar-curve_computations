import GegenbauerFock.PhyslibTraceClassGeometricTail

/-!
# V007 — quantitative geometric tails with common certified kernel proof

The already independently certified module
`PhyslibTraceClassGeometricTail` proves the exact geometric
trace-norm and operator-norm truncation bounds for the nonunital
geometric powers of an arbitrary CFC trace-class operator.

This module exposes those results under their original alternate
API names. It intentionally reuses the verified kernel proofs,
rather than duplicating the former expensive real tsum
calculation, which exhausted Lean's heartbeat limit.
No positivity, finite rank, normality or trace-class identity is
assumed. The two aliases receive independent axiom audits.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual CFC S₁ geometric truncation error for ‖T‖₁ < 1. -/
theorem positivePowers_traceNorm_tail_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    traceNorm H
        ((∑' n : ℕ, positivePower T n) -
          (∑ n ∈ Finset.range N, positivePower T n)) ≤
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) :=
  positivePowers_traceNorm_error_le_geometric T hsmall N

/-- The same geometric majorant for ambient operator norm. -/
theorem positivePowers_operatorNorm_tail_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    ‖((∑' n : ℕ, positivePower T n) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, positivePower T n) : TraceClass H).1‖ ≤
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) :=
  positivePowers_operatorNorm_error_le_geometric T hsmall N

#print axioms ProbabilisticTheory.TraceClass.positivePowers_traceNorm_tail_le
#print axioms ProbabilisticTheory.TraceClass.positivePowers_operatorNorm_tail_le

end ProbabilisticTheory.TraceClass
