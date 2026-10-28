import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — quantitative embedding of Schatten S₁ into bounded operators

This is the first metric bridge required for Banach completeness.
The map forgetting the trace-class witness is contractive: the
ambient operator norm is bounded by the CFC-absolute trace norm.
More strongly, distances between arbitrary trace-class elements
dominate the distances of their underlying bounded operators.

The result is **not** a proof of completeness of S₁. It only
provides the fundamental metric domination used to construct
operator-norm limits from S₁-Cauchy sequences. The required
trace-norm lower semicontinuity remains a separate obligation.

No change to existing certified modules, toolchains or V097.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The natural inclusion S₁(H) -> B(H) is contractive in norm. -/
theorem operator_norm_le_trace_norm (T : TraceClass H) :
    ‖T.1‖ ≤ ‖T‖ := by
  calc
    ‖T.1‖ ≤ ProbabilisticTheory.traceNorm T.1 T.2 :=
      ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs T.1 T.2
    _ = ‖T‖ := (norm_eq_genuineTraceNorm T).symm

/-- The operator-norm distance between arbitrary S₁ elements is
bounded by their genuine trace-norm distance. -/
theorem operator_sub_norm_le_trace_sub_norm (T V : TraceClass H) :
    ‖T.1 - V.1‖ ≤ ‖T - V‖ := by
  simpa only [sub_operator] using operator_norm_le_trace_norm (T - V)

/-- In particular the operator inclusion is nonexpansive for the
metrics induced by the respective norms. -/
theorem operator_dist_le_trace_dist (T V : TraceClass H) :
    dist T.1 V.1 ≤ dist T V := by
  simpa only [dist_eq_norm] using operator_sub_norm_le_trace_sub_norm T V

#print axioms ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm
#print axioms ProbabilisticTheory.TraceClass.operator_sub_norm_le_trace_sub_norm
#print axioms ProbabilisticTheory.TraceClass.operator_dist_le_trace_dist

end ProbabilisticTheory.TraceClass
