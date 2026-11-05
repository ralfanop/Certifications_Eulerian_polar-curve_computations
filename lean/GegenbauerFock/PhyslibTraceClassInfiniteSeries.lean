import GegenbauerFock.PhyslibTraceClassComplete

/-!
# V007 — absolutely convergent CFC Schatten-S₁ operator series

The genuine functional-calculus Schatten trace class is now a
kernel-certified complex Banach space. Consequently a family of
arbitrary trace-class operators whose true CFC trace norms are
summable is itself summable IN the trace-class Banach space.

This module derives the quantitative trace-norm inequality for the
infinite sum, with no positivity, finite-rank, self-adjointness,
commutativity, or preferred basis assumptions.

Do not confuse summability in trace norm with the weaker
operator-norm convergence; the result explicitly uses the newly
certified CompleteSpace (TraceClass H) instance.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Absolute summability of actual CFC trace norms guarantees
summability of the operators in the trace-norm Banach topology. -/
theorem summable_of_summable_traceNorm
    {ι : Type*} (T : ι → TraceClass H)
    (hT : Summable (fun i : ι => traceNorm H (T i))) :
    Summable T := by
  apply Summable.of_norm
  simpa only [norm_eq_genuineTraceNorm] using hT

/-- The trace norm of the Banach-space sum is at most the sum of
the trace norms, including infinite and noncommuting families. -/
theorem traceNorm_tsum_le_tsum_traceNorm
    {ι : Type*} (T : ι → TraceClass H)
    (hT : Summable (fun i : ι => traceNorm H (T i))) :
    traceNorm H (∑' i : ι, T i) ≤
      ∑' i : ι, traceNorm H (T i) := by
  calc
    traceNorm H (∑' i : ι, T i) = ‖∑' i : ι, T i‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ ≤ ∑' i : ι, ‖T i‖ :=
      norm_tsum_le_tsum_norm (by
        simpa only [norm_eq_genuineTraceNorm] using hT)
    _ = ∑' i : ι, traceNorm H (T i) := by
      simp only [norm_eq_genuineTraceNorm]

#print axioms ProbabilisticTheory.TraceClass.summable_of_summable_traceNorm
#print axioms ProbabilisticTheory.TraceClass.traceNorm_tsum_le_tsum_traceNorm

end ProbabilisticTheory.TraceClass
