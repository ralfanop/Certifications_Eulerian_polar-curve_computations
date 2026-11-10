import SpecialImaginaryPoint.V14119Priority3FredholmSectorFunctional

/-!
# Manuscript 14.119 Priority 3 — genuine complex diagonal Schatten S₁ operators

This module extends the previously certified positive real diagonal
sector to arbitrary complex, absolutely summable diagonal coefficients.
These operators need not be self-adjoint or positive. All operatorial
sums and errors live in the genuine CFC-absolute V007 Schatten S₁
Banach space, not an auxiliary diagonal sequence space.

The unit rank-one projections are actual Hilbert-space maps, with
CFC trace norm exactly one. Consequently each arbitrary complex
spectral summand has genuine trace norm equal to the absolute value
of its coefficient. The infinite operator is identified with the
S₁ Banach sum and has the prescribed action on the complete basis.

This is not a construction of the universal Fredholm determinant
on all of S₁(H), nor a differential L²(0,1) realisation.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexDiagonalFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- A unit-mass, finite-support positive real diagonal datum,
used only to construct genuine rank-one Schatten S₁ projectors. -/
def spike (n : ℕ) : Manuscript14Priority3.PositiveDiagonalFredholm.Data where
  coeff k := if k = n then 1 else 0
  nonneg k := by
    split_ifs <;> norm_num
  summable := by
    apply summable_of_ne_finset_zero (s := {n})
    intro k hk
    have hne : k ≠ n := by simpa using hk
    simp [hne]

/-- The actual rank-one orthogonal projection onto the n-th
Hilbert basis vector, as a genuine CFC Schatten S₁ element. -/
def projector (n : ℕ) : ProbabilisticTheory.TraceClass H :=
  Manuscript14Priority3.PositiveDiagonalFredholm.S1term (spike n) n

theorem projector_operator (n : ℕ) :
    (projector n).1 = rankOne ℂ (b n) (b n) := by
  change (((spike n).coeff n : ℝ) : ℂ) •
    rankOne ℂ (b n) (b n) = _
  simp [spike]

theorem projector_traceNorm_eq_one (n : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H (projector n) = 1 := by
  simpa only [projector, spike, if_pos (Eq.refl n)] using
    (Manuscript14Priority3.PositiveDiagonalFredholm.S1term_traceNorm_eq (spike n) n)

theorem projector_norm_eq_one (n : ℕ) : ‖projector n‖ = 1 := by
  rw [ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm]
  exact projector_traceNorm_eq_one n

/-- Arbitrary complex summable spectral data. Absolute summability
is essential; conditional complex summability alone is insufficient. -/
structure Data where
  coeff : ℕ → ℂ
  summableNorm : Summable (fun n : ℕ => ‖coeff n‖)

/-- An actual non-self-adjoint rank-one bounded operator. -/
def operatorTerm (D : Data) (n : ℕ) : H →L[ℂ] H :=
  D.coeff n • rankOne ℂ (b n) (b n)

theorem operatorTerm_norm (D : Data) (n : ℕ) :
    ‖operatorTerm D n‖ = ‖D.coeff n‖ := by
  unfold operatorTerm
  rw [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one n]
  simp

theorem operatorTerm_summable (D : Data) :
    Summable (operatorTerm D) := by
  apply Summable.of_norm
  exact D.summableNorm.congr (fun n => (operatorTerm_norm D n).symm)

/-- The bounded complex-diagonal operator defined by a genuine
operator-norm summable series, not by formal eigenvalue labels. -/
def boundedDiagonal (D : Data) : H →L[ℂ] H :=
  ∑' n : ℕ, operatorTerm D n

theorem boundedDiagonal_eigen (D : Data) (n : ℕ) :
    boundedDiagonal D (b n) = D.coeff n • b n := by
  unfold boundedDiagonal
  rw [tsum_apply (operatorTerm_summable D) (b n)]
  rw [tsum_eq_single n]
  · change (D.coeff n • rankOne ℂ (b n) (b n)) (b n) =
        D.coeff n • b n
    rw [smul_apply, rankOne_apply]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  · intro k hk
    change (D.coeff k • rankOne ℂ (b k) (b k)) (b n) = 0
    rw [smul_apply, rankOne_apply, b.orthonormal.inner_eq_zero hk]
    simp

/-- An arbitrary complex diagonal rank-one summand in the actual S₁ space. -/
def S1term (D : Data) (n : ℕ) : ProbabilisticTheory.TraceClass H :=
  D.coeff n • projector n

theorem S1term_operator (D : Data) (n : ℕ) :
    (S1term D n).1 = operatorTerm D n := by
  change D.coeff n • (projector n).1 = operatorTerm D n
  rw [projector_operator]
  rfl

/-- Exact true CFC Schatten-S₁ norm of an arbitrary complex rank-one
spectral summand: no positivity or self-adjointness assumption. -/
theorem S1term_norm (D : Data) (n : ℕ) :
    ‖S1term D n‖ = ‖D.coeff n‖ := by
  rw [S1term, norm_smul, projector_norm_eq_one, mul_one]

theorem S1term_traceNorm (D : Data) (n : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H (S1term D n) =
      ‖D.coeff n‖ := by
  rw [← ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm]
  exact S1term_norm D n

theorem S1term_norm_summable (D : Data) :
    Summable (fun n : ℕ =>
      ProbabilisticTheory.TraceClass.traceNorm H (S1term D n)) :=
  D.summableNorm.congr (fun n => (S1term_traceNorm D n).symm)

/-- The genuine CFC Schatten S₁ Banach sum for arbitrary
complex absolutely summable diagonals. -/
def S1Diagonal (D : Data) : ProbabilisticTheory.TraceClass H :=
  ∑' n : ℕ, S1term D n

theorem S1term_partial_sum_operator (D : Data) (N : ℕ) :
    ((∑ n ∈ Finset.range N, S1term D n) :
      ProbabilisticTheory.TraceClass H).1 =
        ∑ n ∈ Finset.range N, operatorTerm D n := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ,
        ProbabilisticTheory.TraceClass.add_operator, ih]
      rw [S1term_operator]

/-- The CFC S₁ Banach sum and the genuine bounded-operator series
define exactly the same infinite-dimensional Hilbert-space operator. -/
theorem S1Diagonal_operator_eq (D : Data) :
    (S1Diagonal D).1 = boundedDiagonal D := by
  have hTrace :=
    ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable
      (S1term D) (S1term_norm_summable D)
  have hS :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, operatorTerm D n) atTop
        (𝓝 (S1Diagonal D).1) := by
    simpa only [S1Diagonal, S1term_partial_sum_operator] using hTrace
  have hOp :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, operatorTerm D n) atTop
        (𝓝 (boundedDiagonal D)) :=
    (operatorTerm_summable D).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hS hOp

/-- Full complex spectral eigenbasis action for the actual S₁ operator. -/
theorem S1Diagonal_eigen (D : Data) (n : ℕ) :
    (S1Diagonal D).1 (b n) = D.coeff n • b n := by
  rw [S1Diagonal_operator_eq]
  exact boundedDiagonal_eigen D n

/-- Arbitrary complex diagonal CFC S₁ truncations converge in the
actual Banach trace-norm topology. -/
theorem S1Diagonal_tendsto (D : Data) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, S1term D n)
      atTop (𝓝 (S1Diagonal D)) :=
  ProbabilisticTheory.TraceClass.partial_sums_tendsto_in_traceNorm
    (S1term D) (S1term_norm_summable D)

/-- Quantitative CFC Schatten S₁ tail estimate for genuinely
non-self-adjoint complex diagonal operators. -/
theorem S1Diagonal_error_le_tail (D : Data) (N : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H
      (S1Diagonal D - ∑ n ∈ Finset.range N, S1term D n) ≤
      ∑' k : ℕ, ‖D.coeff (k + N)‖ := by
  have h :=
    ProbabilisticTheory.TraceClass.traceNorm_series_error_le_tsum_tail
      (S1term D) (S1term_norm_summable D) N
  simpa only [S1Diagonal, S1term_traceNorm] using h

#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.projector_traceNorm_eq_one
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1term_traceNorm
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1term_norm_summable
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1Diagonal_operator_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1Diagonal_eigen
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1Diagonal_tendsto
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.S1Diagonal_error_le_tail

end Manuscript14Priority3.ComplexDiagonalFredholm
