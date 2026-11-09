import SpecialImaginaryPoint.V14119Priority3RankOneS1
import GegenbauerFock.PhyslibTraceClassSeriesTailEstimate

/-!
# Manuscript 14.119 Priority 3 — genuine S₁ convergence of finite Dirichlet compressions

This is NOT a determinant definition. We apply the established V007
complete CFC-absolute Schatten-S₁ Banach-space theory to the *actual*
rank-one terms of the previously certified positive Dirichlet inverse
on complex ℓ². It proves the finite spectral truncations converge
in the genuine trace norm with exact scalar tail bounds.

The PDE unitary identification on L²(0,1), the basis-independent
Fredholm determinant and the zeta determinant remain separate
proof obligations; convergence of one Hilbert-basis compression
sequence alone does not settle all three.
-/

noncomputable section

namespace Manuscript14Priority3.TraceClassModel
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp

/-- The actual CFC-absolute trace-class *element* representing each
Dirichlet rank-one inverse spectral summand. -/
def S1term (n : ℕ) : ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.ofOperator H (term n) (term_isTraceClass n)

theorem S1term_traceNorm_eq (n : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H (S1term n) = σ n :=
  term_traceNorm_eq n

theorem S1term_norm_summable :
    Summable (fun n : ℕ => ProbabilisticTheory.TraceClass.traceNorm H (S1term n)) :=
  σ_summable.congr (fun n => (S1term_traceNorm_eq n).symm)

/-- Finite sums of actual S₁ operators are exactly the genuine
finite-rank truncations of the previously constructed bounded operator. -/
theorem S1term_partial_sum_operator (N : ℕ) :
    ((∑ n ∈ Finset.range N, S1term n) : ProbabilisticTheory.TraceClass H).1 =
      ∑ n ∈ Finset.range N, term n := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ,
        ProbabilisticTheory.TraceClass.add_operator, ih]
      rfl

/-- The genuine Schatten-S₁ Banach sum has as its underlying operator
the ACTUAL infinite-dimensional Dirichlet spectral inverse. -/
theorem S1sum_operator_eq_inverse :
    ((∑' n : ℕ, S1term n) : ProbabilisticTheory.TraceClass H).1 = inverse := by
  have hTrace :=
    ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable
      S1term S1term_norm_summable
  have hS :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term n) atTop
        (𝓝 (((∑' n : ℕ, S1term n) : ProbabilisticTheory.TraceClass H).1)) := by
    simpa only [S1term_partial_sum_operator] using hTrace
  have hOp :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term n) atTop (𝓝 inverse) :=
    term_summable.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hS hOp

/-- Every trace-norm truncation error of the *actual* inverse S₁
series is bounded by the mass of the remaining positive eigenvalues. -/
theorem S1_truncation_traceNorm_le_tail (N : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H
      ((∑' n : ℕ, S1term n) - (∑ n ∈ Finset.range N, S1term n)) ≤
      ∑' k : ℕ, σ (k + N) := by
  have h := ProbabilisticTheory.TraceClass.traceNorm_series_error_le_tsum_tail
    S1term S1term_norm_summable N
  simpa only [S1term_traceNorm_eq] using h

/-- Genuine trace-norm convergence of the finite spectral compressions
to the infinite-dimensional S₁ inverse, not merely operator norm. -/
theorem S1_truncation_traceNorm_tendsto_zero :
    Tendsto
      (fun N : ℕ => ProbabilisticTheory.TraceClass.traceNorm H
        ((∑' n : ℕ, S1term n) - (∑ n ∈ Finset.range N, S1term n)))
      atTop (𝓝 0) :=
  ProbabilisticTheory.TraceClass.traceNorm_partial_sum_error_tendsto_zero
    S1term S1term_norm_summable

/-- The exact spectral tail also bounds the true operator-norm error
of the same genuine Hilbert-space inverse truncation. -/
theorem inverse_operatorNorm_error_le_tail (N : ℕ) :
    ‖inverse - (∑ n ∈ Finset.range N, term n)‖ ≤
      ∑' k : ℕ, σ (k + N) := by
  have h := ProbabilisticTheory.TraceClass.operatorNorm_series_error_le_tsum_tail
    S1term S1term_norm_summable N
  simpa only [S1sum_operator_eq_inverse, S1term_partial_sum_operator,
    S1term_traceNorm_eq] using h

#print axioms Manuscript14Priority3.TraceClassModel.S1term_traceNorm_eq
#print axioms Manuscript14Priority3.TraceClassModel.S1term_norm_summable
#print axioms Manuscript14Priority3.TraceClassModel.S1term_partial_sum_operator
#print axioms Manuscript14Priority3.TraceClassModel.S1sum_operator_eq_inverse
#print axioms Manuscript14Priority3.TraceClassModel.S1_truncation_traceNorm_le_tail
#print axioms Manuscript14Priority3.TraceClassModel.S1_truncation_traceNorm_tendsto_zero
#print axioms Manuscript14Priority3.TraceClassModel.inverse_operatorNorm_error_le_tail

end Manuscript14Priority3.TraceClassModel
