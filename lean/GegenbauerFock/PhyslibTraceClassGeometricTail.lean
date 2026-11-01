import GegenbauerFock.PhyslibTraceClassGeometricPowers
import GegenbauerFock.PhyslibTraceClassSeriesTailEstimate

/-!
# V007 — explicit geometric truncation error in the true CFC Schatten S₁

For an arbitrary (not necessarily positive, normal, or compactly
supported) trace-class element T with ‖T‖₁ < 1, the nonunital
geometric series ∑_{n≥0} T^(n+1) has finite-truncation error
bounded by ‖T‖₁^(N+1)/(1-‖T‖₁). The same explicit scalar bound
controls the ambient operator norm.

No unit in S₁ is assumed. This module is an independent candidate
until its exact-SHA pinned Lean compilation and axiom audit succeed.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem positivePower_scalar_geometric_tail
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    (∑' k : ℕ, ‖T‖ ^ (k + N + 1)) =
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  have hpow (k : ℕ) :
      ‖T‖ ^ (k + N + 1) = ‖T‖ ^ k * ‖T‖ ^ (N + 1) := by
    rw [Nat.add_assoc, pow_add]
  simp_rw [hpow]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg T) hsmall]
  rw [div_eq_mul_inv]
  ring

private theorem positivePower_traceNorm_tail_le_scalar_tail
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    (∑' k : ℕ, traceNorm H (positivePower T (k + N))) ≤
      ∑' k : ℕ, ‖T‖ ^ (k + N + 1) := by
  have htail :
      Summable (fun k : ℕ => traceNorm H (positivePower T (k + N))) :=
    (summable_nat_add_iff N).2 (positivePowers_traceNorm_summable T hsmall)
  have hbase : Summable (fun k : ℕ => ‖T‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg T) hsmall
  have hgeom :
      Summable (fun k : ℕ => ‖T‖ ^ (k + N + 1)) := by
    simpa only [Nat.add_assoc] using
      ((summable_nat_add_iff (N + 1)).2 hbase)
  apply htail.tsum_le_tsum _ hgeom
  intro k
  change ‖positivePower T (k + N)‖ ≤ ‖T‖ ^ (k + N + 1)
  exact norm_positivePower_le T (k + N)

/-- A nonunital geometric series has an explicit geometric rate of
convergence in the genuine CFC trace norm. -/
theorem positivePowers_traceNorm_error_le_geometric
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    traceNorm H ((∑' n : ℕ, positivePower T n) -
      (∑ n ∈ Finset.range N, positivePower T n)) ≤
        ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  calc
    traceNorm H ((∑' n : ℕ, positivePower T n) -
      (∑ n ∈ Finset.range N, positivePower T n)) ≤
      ∑' k : ℕ, traceNorm H (positivePower T (k + N)) :=
        traceNorm_series_error_le_tsum_tail
          (fun n => positivePower T n)
          (positivePowers_traceNorm_summable T hsmall) N
    _ ≤ ∑' k : ℕ, ‖T‖ ^ (k + N + 1) :=
      positivePower_traceNorm_tail_le_scalar_tail T hsmall N
    _ = ‖T‖ ^ (N + 1) / (1 - ‖T‖) :=
      positivePower_scalar_geometric_tail T hsmall N

/-- The identical explicit geometric rate also bounds the
operator norm of the error on the original Hilbert space. -/
theorem positivePowers_operatorNorm_error_le_geometric
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    ‖((∑' n : ℕ, positivePower T n) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, positivePower T n) : TraceClass H).1‖ ≤
        ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  calc
    ‖((∑' n : ℕ, positivePower T n) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, positivePower T n) : TraceClass H).1‖ ≤
      traceNorm H ((∑' n : ℕ, positivePower T n) -
        (∑ n ∈ Finset.range N, positivePower T n)) :=
      operatorNorm_series_error_le_traceNorm_series_error
        (fun n => positivePower T n) N
    _ ≤ ‖T‖ ^ (N + 1) / (1 - ‖T‖) :=
      positivePowers_traceNorm_error_le_geometric T hsmall N

#print axioms ProbabilisticTheory.TraceClass.positivePowers_traceNorm_error_le_geometric
#print axioms ProbabilisticTheory.TraceClass.positivePowers_operatorNorm_error_le_geometric

end ProbabilisticTheory.TraceClass
