import GegenbauerFock.PhyslibTraceClassSeriesApproximation
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding

/-!
# V007 — operator-norm convergence of absolutely summable S₁ series

The genuine CFC trace-class space is now certified as a Banach
space. For an absolutely trace-norm summable series of arbitrary
trace-class operators, the S₁ sum is a genuine bounded-operator
limit of its partial sums. The proof gives explicit norm-error
domination by the actual CFC trace-norm remainder.

This result is separate from the certified Banach completeness
instance and uses no positivity, basis, finite-rank or spectral
assumptions. It requires independent exact-SHA Lean compilation.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass
open scoped Topology
open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient operator-norm truncation error is bounded pointwise
by the trace-norm truncation error of the same infinite series. -/
theorem operatorNorm_series_error_le_traceNorm_series_error
    (T : ℕ → TraceClass H)
    (N : ℕ) :
    ‖((∑' n : ℕ, T n) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, T n) : TraceClass H).1‖ ≤
      traceNorm H ((∑' n : ℕ, T n) -
        (∑ n ∈ Finset.range N, T n)) := by
  have h := operator_norm_le_trace_norm
    ((∑' n : ℕ, T n) - (∑ n ∈ Finset.range N, T n))
  simpa only [sub_operator, norm_eq_genuineTraceNorm] using h

/-- For any absolutely S₁-norm summable series, the underlying
bounded operators of its partial sums converge in operator norm
to the underlying bounded operator of its S₁ Banach sum. -/
theorem operator_partial_sums_tendsto_of_traceNorm_summable
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n))) :
    Tendsto (fun N => ((∑ n ∈ Finset.range N, T n) : TraceClass H).1)
      atTop (𝓝 (((∑' n : ℕ, T n) : TraceClass H).1)) := by
  have htrace := traceNorm_partial_sum_error_tendsto_zero T hT
  have hopBound : ∀ N : ℕ,
      ‖((∑' n : ℕ, T n) : TraceClass H).1 -
        ((∑ n ∈ Finset.range N, T n) : TraceClass H).1‖ ≤
        traceNorm H ((∑' n : ℕ, T n) -
          (∑ n ∈ Finset.range N, T n)) :=
    operatorNorm_series_error_le_traceNorm_series_error T
  have hopZero : Tendsto
      (fun N => ‖((∑' n : ℕ, T n) : TraceClass H).1 -
        ((∑ n ∈ Finset.range N, T n) : TraceClass H).1‖)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun N => norm_nonneg _) hopBound htrace
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, norm_sub_rev] using hopZero

#print axioms ProbabilisticTheory.TraceClass.operatorNorm_series_error_le_traceNorm_series_error
#print axioms ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable

end ProbabilisticTheory.TraceClass
