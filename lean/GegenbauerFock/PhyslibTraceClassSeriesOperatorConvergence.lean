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
  have hsum := partial_sums_tendsto_in_traceNorm T hT
  have hcontinuous := (operator_uniformContinuous (H := H)).continuous
  exact hcontinuous.continuousAt.tendsto.comp hsum

/-- Applying the absolutely convergent Schatten-S₁ series to any
fixed Hilbert vector preserves convergence, with the same
bounded-operator sum. No assumption on the selected vector. -/
theorem operator_series_pointwise_tendsto
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n)))
    (x : H) :
    Tendsto
      (fun N => (((∑ n ∈ Finset.range N, T n) : TraceClass H).1) x)
      atTop
      (𝓝 ((((∑' n : ℕ, T n) : TraceClass H).1) x)) := by
  have hop := operator_partial_sums_tendsto_of_traceNorm_summable T hT
  have hev : Continuous (fun A : H →L[ℂ] H => A x) :=
    (ContinuousLinearMap.apply ℂ H x).continuous
  exact hev.continuousAt.tendsto.comp hop

#print axioms ProbabilisticTheory.TraceClass.operator_series_pointwise_tendsto

#print axioms ProbabilisticTheory.TraceClass.operatorNorm_series_error_le_traceNorm_series_error
#print axioms ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable

end ProbabilisticTheory.TraceClass
