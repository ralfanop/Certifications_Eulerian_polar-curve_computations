import GegenbauerFock.PhyslibTraceClassPositivePowers
import GegenbauerFock.PhyslibTraceClassSeriesOperatorConvergence

/-!
# V007 — convergent nonunital geometric powers in the true CFC trace norm

For any actual CFC trace-class operator T with ‖T‖₁ < 1, the
nonunital power series ∑_(n≥0) T^(n+1) is absolutely convergent
in the **genuine Schatten-S₁ norm**, and its partial sums also
converge in the ambient bounded-operator norm.

This is a geometric-series application of the independently
certified nonpositive product bound, the exact CFC trace-class
Banach space, and the series limit theorems. We do not assume
the identity belongs to S₁, nor that T is positive or normal.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass
open scoped Topology

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every strict CFC S₁ contraction has an absolutely convergent
series of nonunital positive powers in its genuine trace norm. -/
theorem positivePowers_traceNorm_summable
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    Summable (fun n : ℕ => traceNorm H (positivePower T n)) := by
  have hgeom : Summable (fun n : ℕ => ‖T‖ ^ (n + 1)) := by
    have h : Summable (fun n : ℕ => ‖T‖ ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg T) hsmall
    exact (summable_nat_add_iff 1).mpr h
  apply Summable.of_nonneg_of_le
  · intro n
    change 0 ≤ ‖positivePower T n‖
    exact norm_nonneg _
  · intro n
    change ‖positivePower T n‖ ≤ ‖T‖ ^ (n + 1)
    exact norm_positivePower_le T n
  · exact hgeom

/-- The CFC Schatten trace-norm error of the partial nonunital
geometric sum tends to zero for every strict trace-norm contraction. -/
theorem positivePowers_traceNorm_remainder_tendsto_zero
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    Filter.Tendsto
      (fun N : ℕ => traceNorm H
        ((∑' n : ℕ, positivePower T n) -
          ∑ n ∈ Finset.range N, positivePower T n))
      Filter.atTop (𝓝 0) :=
  traceNorm_partial_sum_error_tendsto_zero
    (fun n => positivePower T n)
    (positivePowers_traceNorm_summable T hsmall)

/-- The underlying bounded-operator geometric series also converges
in operator norm, not merely in the weaker strong topology. -/
theorem positivePowers_operator_tendsto
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((∑ n ∈ Finset.range N, positivePower T n) : TraceClass H).1)
      Filter.atTop
      (𝓝 ((∑' n : ℕ, positivePower T n : TraceClass H)).1) :=
  operator_partial_sums_tendsto_of_traceNorm_summable
    (fun n => positivePower T n)
    (positivePowers_traceNorm_summable T hsmall)

#print axioms ProbabilisticTheory.TraceClass.positivePowers_traceNorm_summable
#print axioms ProbabilisticTheory.TraceClass.positivePowers_traceNorm_remainder_tendsto_zero
#print axioms ProbabilisticTheory.TraceClass.positivePowers_operator_tendsto

end ProbabilisticTheory.TraceClass
