import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — reverse triangle inequality for the genuine CFC trace norm

The abstract complex Schatten S₁ space has now acquired its *real*
CFC trace norm via the independently verified NormedAddCommGroup
instance. This module extracts the useful quantitative estimate
on the actual proof-carrying trace-class operators, without
assuming Banach completeness or finite dimension.

For any T,V in S₁, the trace norms differ by at most ‖T-V‖₁.
This is a direct consequence of the genuine NormedAddCommGroup
triangle inequality; it is not an operator-norm surrogate.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reverse triangle inequality for the genuine functional-calculus
Schatten trace norm, on arbitrary complex Hilbert spaces. -/
theorem traceNorm_reverse_triangle_v007
    (T V : TraceClass H) :
    |traceNorm H T - traceNorm H V| ≤ traceNorm H (T - V) := by
  have h₁ : ‖T‖ - ‖V‖ ≤ ‖T - V‖ := norm_sub_norm_le T V
  have h₂ : ‖V‖ - ‖T‖ ≤ ‖T - V‖ := by
    simpa only [norm_sub_rev] using (norm_sub_norm_le V T)
  change |‖T‖ - ‖V‖| ≤ ‖T - V‖
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- The CFC trace norm is nonexpansive with respect to the very
trace-norm metric it induces, for arbitrary nonpositive operators. -/
theorem traceNorm_dist_le_v007 (T V : TraceClass H) :
    dist (traceNorm H T) (traceNorm H V) ≤ dist T V := by
  simpa only [Real.dist_eq, Real.norm_eq_abs, dist_eq_norm,
    norm_eq_genuineTraceNorm] using
    (traceNorm_reverse_triangle_v007 T V)

#print axioms ProbabilisticTheory.TraceClass.traceNorm_reverse_triangle_v007
#print axioms ProbabilisticTheory.TraceClass.traceNorm_dist_le_v007

end ProbabilisticTheory.TraceClass
