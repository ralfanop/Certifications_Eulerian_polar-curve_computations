import SpecialImaginaryPoint.V14119Priority3ComplexDiagonalS1
import GegenbauerFock.PhyslibTraceClassSandwichContinuous
import GegenbauerFock.PhyslibTraceClassSeriesTailEstimate

/-!
# Manuscript 14.119 Priority 3 — arbitrary nuclear rank-one CFC S₁ series

For ANY two complex Hilbert vectors u,v in the actual ℓ² space
(not necessarily basis vectors), construct |u⟩⟨v| as a genuine
CFC-absolute Schatten-S₁ element by sandwiching an existing
certified unit-mass rank-one CFC-S₁ projector by bounded operators.

The sharp S₁ ideal estimate and opposite operator-norm inequality
then give the EXACT identity
  ‖|u⟩⟨v|‖₁ = ‖u‖ ‖v‖.

As a result every nuclear rank-one series with summable costs
∑ ‖u_n‖‖v_n‖ converges in the genuine CFC S₁ Banach norm,
represents the actual operator-norm Hilbert series, and has a
quantitative trace-norm truncation error.

The theorem DOES NOT yet assert that *all* CFC S₁ maps admit
such a rank-one decomposition; that is the remaining S₁ finite
rank density / S₂ factorization-tail obligation. No general
basis-independent infinite Fredholm determinant is defined here.
-/

noncomputable section

namespace Manuscript14Priority3.NuclearRankOne
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Genuine rank-one Hilbert operator as a CFC Schatten-S₁ element,
without any special basis assumption on u and v. -/
def rankOneS1 (u v : H) : ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.sandwich
    (Manuscript14Priority3.ComplexDiagonalFredholm.projector 0)
    (rankOne ℂ u (b 0))
    (rankOne ℂ (b 0) v)

/-- The construction is the ACTUAL Hilbert rank-one operator,
not merely an auxiliary sequence or formal tensor. -/
theorem rankOneS1_operator (u v : H) :
    (rankOneS1 u v).1 = rankOne ℂ u v := by
  change
    (rankOne ℂ u (b 0)) *
    (Manuscript14Priority3.ComplexDiagonalFredholm.projector 0).1 *
    (rankOne ℂ (b 0) v) = rankOne ℂ u v
  rw [Manuscript14Priority3.ComplexDiagonalFredholm.projector_operator]
  change
    ((rankOne ℂ u (b 0)).comp (rankOne ℂ (b 0) (b 0))).comp
      (rankOne ℂ (b 0) v) = rankOne ℂ u v
  simp [rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one]

/-- Sharp CFC trace-norm UPPER bound for arbitrary rank-one maps,
obtained from the genuine bilaterally ideal S₁ norm. -/
theorem rankOneS1_norm_le (u v : H) :
    ‖rankOneS1 u v‖ ≤ ‖u‖ * ‖v‖ := by
  let A : H →L[ℂ] H := rankOne ℂ u (b 0)
  let B : H →L[ℂ] H := rankOne ℂ (b 0) v
  let P : ProbabilisticTheory.TraceClass H :=
    Manuscript14Priority3.ComplexDiagonalFredholm.projector 0
  change ‖ProbabilisticTheory.TraceClass.sandwichContinuous A B P‖ ≤
    ‖u‖ * ‖v‖
  calc
    ‖ProbabilisticTheory.TraceClass.sandwichContinuous A B P‖ ≤
        ‖ProbabilisticTheory.TraceClass.sandwichContinuous A B‖ * ‖P‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖A‖ * ‖B‖) * ‖P‖ :=
      mul_le_mul_of_nonneg_right
        (ProbabilisticTheory.TraceClass.sandwichContinuous_norm_le A B)
        (norm_nonneg _)
    _ = ‖u‖ * ‖v‖ := by
      simp [A, B, P,
        Manuscript14Priority3.ComplexDiagonalFredholm.projector_norm_eq_one,
        b.orthonormal.norm_eq_one, norm_rankOne]

/-- EXACT CFC Schatten-S₁ trace norm for arbitrary nonnormal
rank-one Hilbert operators, including nonorthogonal vectors. -/
theorem rankOneS1_norm_eq (u v : H) :
    ‖rankOneS1 u v‖ = ‖u‖ * ‖v‖ := by
  apply le_antisymm (rankOneS1_norm_le u v)
  calc
    ‖u‖ * ‖v‖ = ‖rankOne ℂ u v‖ := (norm_rankOne u v).symm
    _ = ‖(rankOneS1 u v).1‖ := by rw [rankOneS1_operator]
    _ ≤ ‖rankOneS1 u v‖ :=
      ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm _

/-- Sharp genuine CFC-absolute trace norm, not the bounded operator norm. -/
theorem rankOneS1_traceNorm_eq (u v : H) :
    ProbabilisticTheory.TraceClass.traceNorm H (rankOneS1 u v) =
      ‖u‖ * ‖v‖ := by
  rw [← ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm]
  exact rankOneS1_norm_eq u v

/-- All nuclear series whose actual rank-one costs are summable
converge in the genuine complete CFC Schatten-S₁ Banach space. -/
theorem rankOne_nuclear_summable
    (u v : ℕ → H)
    (hcost : Summable (fun n : ℕ => ‖u n‖ * ‖v n‖)) :
    Summable (fun n : ℕ => rankOneS1 (u n) (v n)) := by
  apply Summable.of_norm
  exact hcost.congr (fun n => (rankOneS1_norm_eq (u n) (v n)).symm)

/-- The underlying actual bounded Hilbert-operator series is
also absolutely convergent in OPERATOR norm. -/
theorem rankOne_operator_summable
    (u v : ℕ → H)
    (hcost : Summable (fun n : ℕ => ‖u n‖ * ‖v n‖)) :
    Summable (fun n : ℕ => rankOne ℂ (u n) (v n) : H →L[ℂ] H) := by
  apply Summable.of_norm
  simpa only [norm_rankOne] using hcost

/-- The genuine S₁ infinite sum has as its actual Hilbert operator
the operator-norm sum of the SAME arbitrary rank-one maps. -/
theorem rankOne_nuclear_operator_eq
    (u v : ℕ → H)
    (hcost : Summable (fun n : ℕ => ‖u n‖ * ‖v n‖)) :
    ((∑' n : ℕ, rankOneS1 (u n) (v n)) :
      ProbabilisticTheory.TraceClass H).1 =
        ∑' n : ℕ, (rankOne ℂ (u n) (v n) : H →L[ℂ] H) := by
  have hnorm : Summable
      (fun n : ℕ =>
        ProbabilisticTheory.TraceClass.traceNorm H
          (rankOneS1 (u n) (v n))) :=
    hcost.congr (fun n => (rankOneS1_traceNorm_eq (u n) (v n)).symm)
  have hTrace :=
    ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable
      (fun n => rankOneS1 (u n) (v n)) hnorm
  have hpartial (N : ℕ) :
      ((∑ n ∈ Finset.range N, rankOneS1 (u n) (v n)) :
        ProbabilisticTheory.TraceClass H).1 =
      ∑ n ∈ Finset.range N,
        (rankOne ℂ (u n) (v n) : H →L[ℂ] H) := by
    induction N with
    | zero => simp
    | succ N ih =>
        simp only [Finset.sum_range_succ,
          ProbabilisticTheory.TraceClass.add_operator, ih]
        rw [rankOneS1_operator]
  have hS :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            (rankOne ℂ (u n) (v n) : H →L[ℂ] H))
        atTop
        (𝓝 (((∑' n : ℕ, rankOneS1 (u n) (v n)) :
          ProbabilisticTheory.TraceClass H).1)) := by
    simpa only [hpartial] using hTrace
  have hOp :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            (rankOne ℂ (u n) (v n) : H →L[ℂ] H))
        atTop
        (𝓝 (∑' n : ℕ, (rankOne ℂ (u n) (v n) : H →L[ℂ] H))) :=
    (rankOne_operator_summable u v hcost).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hS hOp

/-- Genuine CFC S₁ truncation bound for arbitrary nuclear
rank-one Hilbert series; no positivity or diagonalizability. -/
theorem rankOne_nuclear_traceNorm_error_le_tail
    (u v : ℕ → H)
    (hcost : Summable (fun n : ℕ => ‖u n‖ * ‖v n‖))
    (N : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H
      ((∑' n : ℕ, rankOneS1 (u n) (v n)) -
       ∑ n ∈ Finset.range N, rankOneS1 (u n) (v n)) ≤
      ∑' k : ℕ, ‖u (k + N)‖ * ‖v (k + N)‖ := by
  have hnorm : Summable
      (fun n : ℕ =>
        ProbabilisticTheory.TraceClass.traceNorm H
          (rankOneS1 (u n) (v n))) :=
    hcost.congr (fun n => (rankOneS1_traceNorm_eq (u n) (v n)).symm)
  have h := ProbabilisticTheory.TraceClass.traceNorm_series_error_le_tsum_tail
    (fun n => rankOneS1 (u n) (v n)) hnorm N
  simpa only [rankOneS1_traceNorm_eq] using h

#print axioms Manuscript14Priority3.NuclearRankOne.rankOneS1_operator
#print axioms Manuscript14Priority3.NuclearRankOne.rankOneS1_norm_le
#print axioms Manuscript14Priority3.NuclearRankOne.rankOneS1_norm_eq
#print axioms Manuscript14Priority3.NuclearRankOne.rankOneS1_traceNorm_eq
#print axioms Manuscript14Priority3.NuclearRankOne.rankOne_nuclear_summable
#print axioms Manuscript14Priority3.NuclearRankOne.rankOne_operator_summable
#print axioms Manuscript14Priority3.NuclearRankOne.rankOne_nuclear_operator_eq
#print axioms Manuscript14Priority3.NuclearRankOne.rankOne_nuclear_traceNorm_error_le_tail

end Manuscript14Priority3.NuclearRankOne
