import GegenbauerFock.PhyslibTraceClassGeometricPowers
import GegenbauerFock.PhyslibTraceClassSeriesTailEstimate

/-!
# V007 — sharp geometric tails for the genuine CFC S₁ trace norm

For a (possibly nonnormal, nonpositive) trace-class T with
‖T‖₁ < 1, every finite truncation of its nonunital geometric
series has an explicit trace-norm error bound:

  ‖∑_{n≥0} T^(n+1) - ∑_{n<N} T^(n+1)‖₁
    ≤ ‖T‖₁^(N+1)/(1-‖T‖₁).

The same sharp scalar majorant controls the weaker bounded-operator
norm. The coefficient 1 is inherited from the genuine submultiplicative
Schatten trace norm and not from finite-rank approximation or positivity.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem positivePowers_scalar_geometric_tail
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    (∑' k : ℕ, ‖T‖ ^ (k + N + 1)) =
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  have hpow (k : ℕ) :
      ‖T‖ ^ (k + N + 1) = ‖T‖ ^ (N + 1) * ‖T‖ ^ k := by
    rw [show k + N + 1 = (N + 1) + k by omega, pow_add]
  calc
    (∑' k : ℕ, ‖T‖ ^ (k + N + 1)) =
        ∑' k : ℕ, ‖T‖ ^ (N + 1) * ‖T‖ ^ k := by
          apply tsum_congr
          intro k
          exact hpow k
    _ = ‖T‖ ^ (N + 1) * (∑' k : ℕ, ‖T‖ ^ k) := by
          rw [tsum_mul_left]
    _ = ‖T‖ ^ (N + 1) * (1 - ‖T‖)⁻¹ := by
          rw [tsum_geometric_of_lt_one (norm_nonneg T) hsmall]
    _ = ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
          rw [div_eq_mul_inv]

/-- Explicit exponential trace-norm tail control for the full
nonunital CFC Schatten geometric series, with no positivity condition. -/
theorem positivePowers_traceNorm_tail_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    traceNorm H
        ((∑' n : ℕ, positivePower T n) -
          (∑ n ∈ Finset.range N, positivePower T n)) ≤
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  have hT : Summable (fun n : ℕ => traceNorm H (positivePower T n)) :=
    positivePowers_traceNorm_summable T hsmall
  have hgeom : Summable (fun n : ℕ => ‖T‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg T) hsmall)
  have hgeomTail : Summable (fun k : ℕ => ‖T‖ ^ (k + N + 1)) :=
    (summable_nat_add_iff N).mpr hgeom
  have htraceTail : Summable (fun k : ℕ =>
      traceNorm H (positivePower T (k + N))) :=
    (summable_nat_add_iff N).mpr hT
  calc
    traceNorm H ((∑' n : ℕ, positivePower T n) -
        (∑ n ∈ Finset.range N, positivePower T n)) ≤
      ∑' k : ℕ, traceNorm H (positivePower T (k + N)) :=
        traceNorm_series_error_le_tsum_tail (fun n => positivePower T n) hT N
    _ ≤ ∑' k : ℕ, ‖T‖ ^ (k + N + 1) :=
      htraceTail.tsum_le_tsum
        (fun k => norm_positivePower_le T (k + N)) hgeomTail
    _ = ‖T‖ ^ (N + 1) / (1 - ‖T‖) :=
      positivePowers_scalar_geometric_tail T hsmall N

/-- The same explicit geometric tail controls the ambient
bounded-operator norm of the underlying Fock-space endomorphisms. -/
theorem positivePowers_operatorNorm_tail_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) (N : ℕ) :
    ‖((∑' n : ℕ, positivePower T n) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, positivePower T n) : TraceClass H).1‖ ≤
      ‖T‖ ^ (N + 1) / (1 - ‖T‖) := by
  exact (operatorNorm_series_error_le_traceNorm_series_error
    (fun n => positivePower T n) N).trans
      (positivePowers_traceNorm_tail_le T hsmall N)

#print axioms ProbabilisticTheory.TraceClass.positivePowers_traceNorm_tail_le
#print axioms ProbabilisticTheory.TraceClass.positivePowers_operatorNorm_tail_le

end ProbabilisticTheory.TraceClass
