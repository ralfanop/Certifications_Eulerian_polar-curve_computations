import GegenbauerFock.PhyslibTraceClassVaryingSandwichSeries
import GegenbauerFock.PhyslibTraceClassSeriesOperatorConvergence

/-!
# V007 — certified-size tails of infinite families with varying multipliers

The weighted trace-norm mass beyond the first N indices controls
both the trace-norm truncation error and the ambient operator-norm
error. Each term may use its own bounded multipliers Aₙ, Bₙ,
and no positivity, normality, commutativity, or finite-rank
assumption is imposed.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace-norm error of a finite truncation of a series with varying
left and right multipliers is bounded by the genuine S₁ mass of
the omitted indices. -/
theorem traceNorm_varying_sandwich_tail_le_v007
    (c : ℕ → ℂ) (A B : ℕ → H →L[ℂ] H) (T : ℕ → TraceClass H)
    (h : Summable (fun n : ℕ =>
      ‖c n‖ * (‖A n‖ * ‖B n‖ * traceNorm H (T n))))
    (N : ℕ) :
    traceNorm H ((∑' n : ℕ, c n • sandwich (T n) (A n) (B n)) -
      (∑ n ∈ Finset.range N, c n • sandwich (T n) (A n) (B n))) ≤
    ∑' k : ℕ, ‖c (k + N)‖ *
      (‖A (k + N)‖ * ‖B (k + N)‖ * traceNorm H (T (k + N))) := by
  have hs := summable_varying_sandwich_series_v007 c A B T h
  have htail : Summable (fun k : ℕ =>
      ‖c (k + N)‖ *
        (‖A (k + N)‖ * ‖B (k + N)‖ *
          traceNorm H (T (k + N)))) :=
    (summable_nat_add_iff N).2 h
  have hsplit :
      (∑' n : ℕ, c n • sandwich (T n) (A n) (B n)) =
        (∑ n ∈ Finset.range N, c n • sandwich (T n) (A n) (B n)) +
        ∑' k : ℕ, c (k + N) •
          sandwich (T (k + N)) (A (k + N)) (B (k + N)) :=
    (hs.sum_add_tsum_nat_add N).symm
  calc
    traceNorm H ((∑' n : ℕ, c n • sandwich (T n) (A n) (B n)) -
      (∑ n ∈ Finset.range N, c n • sandwich (T n) (A n) (B n))) =
        ‖(∑' n : ℕ, c n • sandwich (T n) (A n) (B n)) -
          (∑ n ∈ Finset.range N, c n • sandwich (T n) (A n) (B n))‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖∑' k : ℕ, c (k + N) •
          sandwich (T (k + N)) (A (k + N)) (B (k + N))‖ := by
      rw [hsplit]
      simp
    _ ≤ ∑' k : ℕ, ‖c (k + N)‖ *
          (‖A (k + N)‖ * ‖B (k + N)‖ *
            traceNorm H (T (k + N))) :=
      tsum_of_norm_bounded htail.hasSum (fun k =>
        norm_weighted_sandwich_le_v007
          (c (k + N)) (T (k + N)) (A (k + N)) (B (k + N)))

/-- The same exact tail bounds truncation in the weaker ambient
operator norm; it remains a true-S₁ estimate, not an ambient
operator-norm interpretation of the trace norm. -/
theorem operatorNorm_varying_sandwich_tail_le_v007
    (c : ℕ → ℂ) (A B : ℕ → H →L[ℂ] H) (T : ℕ → TraceClass H)
    (h : Summable (fun n : ℕ =>
      ‖c n‖ * (‖A n‖ * ‖B n‖ * traceNorm H (T n))))
    (N : ℕ) :
    ‖((∑' n : ℕ, c n • sandwich (T n) (A n) (B n)) : TraceClass H).1 -
      ((∑ n ∈ Finset.range N, c n • sandwich (T n) (A n) (B n)) :
        TraceClass H).1‖ ≤
    ∑' k : ℕ, ‖c (k + N)‖ *
      (‖A (k + N)‖ * ‖B (k + N)‖ * traceNorm H (T (k + N))) := by
  exact (operatorNorm_series_error_le_traceNorm_series_error
      (fun n => c n • sandwich (T n) (A n) (B n)) N).trans
    (traceNorm_varying_sandwich_tail_le_v007 c A B T h N)

#print axioms ProbabilisticTheory.TraceClass.traceNorm_varying_sandwich_tail_le_v007
#print axioms ProbabilisticTheory.TraceClass.operatorNorm_varying_sandwich_tail_le_v007

end ProbabilisticTheory.TraceClass
