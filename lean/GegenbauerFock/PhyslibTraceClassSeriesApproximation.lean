import GegenbauerFock.PhyslibTraceClassInfiniteSeries

/-!
# V007 — trace-norm convergence of partial sums in the genuine S₁ Banach space

For a series of arbitrary trace-class operators whose *actual CFC
trace norms* are summable, the operator partial sums converge in
Schatten-S₁ norm to their Banach sum. In particular, the genuine
trace norm of the truncation error tends to zero.

This is stronger than convergence in the ambient operator norm.
No positivity, finite-rank hypothesis, self-adjointness, special
Hilbert basis, or new axiom is needed.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass
open scoped Topology
open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine trace-norm convergence of all partial sums of an
absolutely trace-norm summable sequence of S₁ endomorphisms. -/
theorem partial_sums_tendsto_in_traceNorm
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n))) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, T n) atTop
      (𝓝 (∑' n : ℕ, T n)) :=
  (summable_of_summable_traceNorm T hT).hasSum.tendsto_sum_nat

/-- The actual CFC S₁ norm of the remainder after N terms
vanishes as N tends to infinity. -/
theorem traceNorm_partial_sum_error_tendsto_zero
    (T : ℕ → TraceClass H)
    (hT : Summable (fun n => traceNorm H (T n))) :
    Tendsto
      (fun N => traceNorm H ((∑' n : ℕ, T n) -
        (∑ n ∈ Finset.range N, T n)))
      atTop (𝓝 0) := by
  have hlim := partial_sums_tendsto_in_traceNorm T hT
  have hdist := tendsto_iff_dist_tendsto_zero.mp hlim
  have hpoint (N : ℕ) :
      traceNorm H ((∑' n : ℕ, T n) -
        (∑ n ∈ Finset.range N, T n)) =
      dist (∑ n ∈ Finset.range N, T n) (∑' n : ℕ, T n) := by
    calc
      traceNorm H ((∑' n : ℕ, T n) -
          (∑ n ∈ Finset.range N, T n)) =
          ‖(∑' n : ℕ, T n) - (∑ n ∈ Finset.range N, T n)‖ :=
        (norm_eq_genuineTraceNorm _).symm
      _ = ‖(∑ n ∈ Finset.range N, T n) - (∑' n : ℕ, T n)‖ :=
        norm_sub_rev _ _
      _ = dist (∑ n ∈ Finset.range N, T n) (∑' n : ℕ, T n) :=
        (dist_eq_norm (∑ n ∈ Finset.range N, T n) (∑' n : ℕ, T n)).symm
  simpa only [← hpoint] using hdist

#print axioms ProbabilisticTheory.TraceClass.partial_sums_tendsto_in_traceNorm
#print axioms ProbabilisticTheory.TraceClass.traceNorm_partial_sum_error_tendsto_zero

end ProbabilisticTheory.TraceClass
