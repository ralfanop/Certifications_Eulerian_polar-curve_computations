import GegenbauerFock.PhyslibTraceClassSeriesOperatorConvergence

/-!
# V007 — quantitative tails of arbitrary CFC Schatten S₁ series

For absolutely trace-norm summable sequences of genuine trace-class
operators, the finite-truncation error is explicitly dominated by
the scalar series of trace norms over the remaining indices.

The same *exact numerical tail* controls the error in ambient
bounded-operator norm; no positivity, commutativity, rank restriction
or choice of eigenbasis is imposed.

This is a new standalone candidate pending its own pinned Lean CI
and #print axioms audits.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For any N, the genuine S₁ error after the first N terms is
bounded by the *actual remaining trace-norm mass*. -/
theorem traceNorm_series_error_le_tsum_tail
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n)))
    (N : ℕ) :
    traceNorm H ((∑' n : ℕ, T n) -
        (∑ n ∈ Finset.range N, T n)) ≤
      ∑' k : ℕ, traceNorm H (T (k + N)) := by
  have hs : Summable T := summable_of_summable_traceNorm T hT
  have htail : Summable (fun k : ℕ => traceNorm H (T (k + N))) :=
    (summable_nat_add_iff N).2 hT
  have hsplit :
      (∑' n : ℕ, T n) =
        (∑ n ∈ Finset.range N, T n) + ∑' k : ℕ, T (k + N) :=
    (hs.sum_add_tsum_nat_add N).symm
  calc
    traceNorm H ((∑' n : ℕ, T n) -
        (∑ n ∈ Finset.range N, T n)) =
        ‖(∑' n : ℕ, T n) - (∑ n ∈ Finset.range N, T n)‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖∑' k : ℕ, T (k + N)‖ := by rw [hsplit]; simp
    _ ≤ ∑' k : ℕ, ‖T (k + N)‖ :=
      norm_tsum_le_tsum_norm (by
        simpa only [norm_eq_genuineTraceNorm] using htail)
    _ = ∑' k : ℕ, traceNorm H (T (k + N)) := by
      simp only [norm_eq_genuineTraceNorm]

/-- The same quantitative numerical tail bounds the stronger
error measured in ambient bounded-operator norm. -/
theorem operatorNorm_series_error_le_tsum_tail
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n)))
    (N : ℕ) :
    ‖((∑' n : ℕ, T n) : TraceClass H).1 -
        ((∑ n ∈ Finset.range N, T n) : TraceClass H).1‖ ≤
      ∑' k : ℕ, traceNorm H (T (k + N)) := by
  exact (operatorNorm_series_error_le_traceNorm_series_error T N).trans
    (traceNorm_series_error_le_tsum_tail T hT N)

#print axioms ProbabilisticTheory.TraceClass.traceNorm_series_error_le_tsum_tail
#print axioms ProbabilisticTheory.TraceClass.operatorNorm_series_error_le_tsum_tail

end ProbabilisticTheory.TraceClass
