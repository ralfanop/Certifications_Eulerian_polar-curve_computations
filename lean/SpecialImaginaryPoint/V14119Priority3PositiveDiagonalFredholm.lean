import SpecialImaginaryPoint.V14119Priority3S1Truncation
import SpecialImaginaryPoint.V14119Priority3OperatorCompression

/-!
# Manuscript 14.119 Priority 3 — a genuine positive diagonal S₁ Fredholm sector

This module constructs an *operatorial*, infinite-dimensional, trace-class
Fredholm determinant on the class of operators diagonal in the fixed
complex Hilbert basis, with arbitrary nonnegative summable diagonal
coefficients. It does not specialize the definition to the Dirichlet
spectrum: the Dirichlet inverse is just one member of this much larger class.

The S₁ carrier and norm are the genuine CFC-absolute Physlib-compatible
V007 objects, and the finite determinants are matrix determinants of
compressions of the actual bounded operator.

The determinant defined here is on the positive diagonal sector, not
the basis-independent Fredholm determinant on *all* Schatten S₁(H).
Extension, basis independence, and a global S₁ continuity estimate
remain independent open theorems, as does the differential L²(0,1)
identification and the relative zeta-regularized determinant.
-/

noncomputable section

namespace Manuscript14Priority3.PositiveDiagonalFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Arbitrary summable nonnegative spectral coefficients.
No fixed Dirichlet spectrum is part of this type. -/
structure Data where
  coeff : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ coeff n
  summable : Summable coeff

/-- Actual infinite-dimensional rank-one bounded operator with
a general nonnegative summable diagonal coefficient. -/
def term (D : Data) (n : ℕ) : H →L[ℂ] H :=
  (D.coeff n : ℂ) • rankOne ℂ (b n) (b n)

theorem term_norm (D : Data) (n : ℕ) : ‖term D n‖ = D.coeff n := by
  change ‖(D.coeff n : ℂ) • rankOne ℂ (b n) (b n)‖ = D.coeff n
  rw [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one n]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.nonneg n)]

theorem term_summable (D : Data) : Summable (term D) := by
  apply Summable.of_norm
  exact D.summable.congr (fun n => (term_norm D n).symm)

/-- Infinite bounded operator defined by the actual rank-one series. -/
def boundedDiagonal (D : Data) : H →L[ℂ] H := ∑' n : ℕ, term D n

theorem boundedDiagonal_eigen (D : Data) (n : ℕ) :
    boundedDiagonal D (b n) = (D.coeff n : ℂ) • b n := by
  unfold boundedDiagonal
  rw [tsum_apply (term_summable D) (b n)]
  rw [tsum_eq_single n]
  · change ((D.coeff n : ℂ) • rankOne ℂ (b n) (b n)) (b n) =
        (D.coeff n : ℂ) • b n
    rw [smul_apply, rankOne_apply]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  · intro k hk
    change ((D.coeff k : ℂ) • rankOne ℂ (b k) (b k)) (b n) = 0
    rw [smul_apply, rankOne_apply, b.orthonormal.inner_eq_zero hk]
    simp

theorem term_isPositive (D : Data) (n : ℕ) :
    (term D n).IsPositive := by
  have hc : (0 : ℂ) ≤ (D.coeff n : ℂ) := by
    exact_mod_cast D.nonneg n
  exact (InnerProductSpace.isPositive_rankOne_self (b n)).smul_of_nonneg hc

theorem boundedDiagonal_nonneg (D : Data) :
    (0 : H →L[ℂ] H) ≤ boundedDiagonal D := by
  have hpart (N : ℕ) :
      (0 : H →L[ℂ] H) ≤ ∑ n ∈ Finset.range N, term D n := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive).2 <|
      ContinuousLinearMap.isPositive_sum (Finset.range N)
        (fun n _ => term_isPositive D n)
  exact isClosed_Ici.mem_of_tendsto
    (term_summable D).hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hpart)

theorem boundedDiagonal_diagonal (D : Data) (n : ℕ) :
    (inner ℂ (b n) (boundedDiagonal D (b n))).re = D.coeff n := by
  rw [boundedDiagonal_eigen D n, inner_smul_right,
    inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  norm_num

/-- Real diagonal of a *single* genuine rank-one Hilbert-space map. -/
theorem term_diagonal (D : Data) (n k : ℕ) :
    (inner ℂ (b k) (term D n (b k))).re =
      if k = n then D.coeff n else 0 := by
  by_cases h : k = n
  · subst k
    change (inner ℂ (b n)
      (((D.coeff n : ℂ) • rankOne ℂ (b n) (b n)) (b n))).re = _
    rw [smul_apply, rankOne_apply]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  · have hnk : n ≠ k := Ne.symm h
    change (inner ℂ (b k)
      (((D.coeff n : ℂ) • rankOne ℂ (b n) (b n)) (b k))).re = _
    rw [smul_apply, rankOne_apply, b.orthonormal.inner_eq_zero hnk]
    simp [h]

theorem term_isTraceClass (D : Data) (n : ℕ) :
    ProbabilisticTheory.IsTraceClass (term D n) := by
  have hpos : (0 : H →L[ℂ] H) ≤ term D n :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2 (term_isPositive D n)
  have hdiag :
      Summable (fun k : ℕ => (inner ℂ (b k) ((term D n) (b k))).re) := by
    apply summable_of_ne_finset_zero (s := {n})
    intro k hk
    rw [term_diagonal]
    have hne : k ≠ n := by simpa using hk
    simp [hne]
  exact GegenbauerFock.Ultraspherical.complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
      (term D n) hpos b hdiag

theorem term_traceNorm_eq (D : Data) (n : ℕ) :
    ProbabilisticTheory.traceNorm (term D n) (term_isTraceClass D n) =
      D.coeff n := by
  have hpos : (0 : H →L[ℂ] H) ≤ term D n :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2 (term_isPositive D n)
  rw [GegenbauerFock.HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
      (term D n) (term_isTraceClass D n) hpos b]
  rw [tsum_eq_single n]
  · simpa using term_diagonal D n n
  · intro k hk
    simpa [hk] using term_diagonal D n k

/-- Concrete element of the *genuine* CFC Schatten S₁ Banach space. -/
def S1term (D : Data) (n : ℕ) : ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.ofOperator H (term D n) (term_isTraceClass D n)

theorem S1term_traceNorm_eq (D : Data) (n : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H (S1term D n) =
      D.coeff n :=
  term_traceNorm_eq D n

theorem S1term_norm_summable (D : Data) :
    Summable (fun n : ℕ =>
      ProbabilisticTheory.TraceClass.traceNorm H (S1term D n)) :=
  D.summable.congr (fun n => (S1term_traceNorm_eq D n).symm)

/-- True S₁ Banach sum of the actual rank-one operators. -/
def S1Diagonal (D : Data) : ProbabilisticTheory.TraceClass H :=
  ∑' n : ℕ, S1term D n

theorem S1term_partial_sum_operator (D : Data) (N : ℕ) :
    ((∑ n ∈ Finset.range N, S1term D n) :
       ProbabilisticTheory.TraceClass H).1 =
        ∑ n ∈ Finset.range N, term D n := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ,
        ProbabilisticTheory.TraceClass.add_operator, ih]
      rfl

/-- Operator underlying the actual S₁ limit equals the actual
infinite bounded diagonal Hilbert-space operator. -/
theorem S1Diagonal_operator_eq (D : Data) :
    (S1Diagonal D).1 = boundedDiagonal D := by
  have hTrace :=
    ProbabilisticTheory.TraceClass.operator_partial_sums_tendsto_of_traceNorm_summable
      (S1term D) (S1term_norm_summable D)
  have hS :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term D n) atTop
        (𝓝 (S1Diagonal D).1) := by
    simpa only [S1Diagonal, S1term_partial_sum_operator] using hTrace
  have hOp :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term D n) atTop
        (𝓝 (boundedDiagonal D)) :=
    (term_summable D).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hS hOp

/-- The true S₁ norm of the complete positive diagonal operator is
exactly the sum of its arbitrary nonnegative summable spectrum. -/
theorem S1Diagonal_traceNorm_eq (D : Data) :
    ProbabilisticTheory.TraceClass.traceNorm H (S1Diagonal D) =
      ∑' n : ℕ, D.coeff n := by
  have hpos : (0 : H →L[ℂ] H) ≤ (S1Diagonal D).1 := by
    rw [S1Diagonal_operator_eq D]
    exact boundedDiagonal_nonneg D
  change ProbabilisticTheory.traceNorm (S1Diagonal D).1 (S1Diagonal D).2 =
    ∑' n : ℕ, D.coeff n
  rw [GegenbauerFock.HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
    (S1Diagonal D).1 (S1Diagonal D).2 hpos b]
  rw [S1Diagonal_operator_eq D]
  exact tsum_congr (boundedDiagonal_diagonal D)

/-- Approximation of the actual operator in the true S₁ Banach topology. -/
theorem S1Diagonal_truncation_tendsto (D : Data) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, S1term D n) atTop
      (𝓝 (S1Diagonal D)) :=
  ProbabilisticTheory.TraceClass.partial_sums_tendsto_in_traceNorm
    (S1term D) (S1term_norm_summable D)

/-- Quantitative true S₁ truncation error for every positive summable
diagonal, with no reliance on the Dirichlet eigenvalue formula. -/
theorem S1Diagonal_error_le_tail (D : Data) (N : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm H
      (S1Diagonal D - ∑ n ∈ Finset.range N, S1term D n) ≤
      ∑' k : ℕ, D.coeff (k + N) := by
  have h := ProbabilisticTheory.TraceClass.traceNorm_series_error_le_tsum_tail
    (S1term D) (S1term_norm_summable D) N
  simpa only [S1Diagonal, S1term_traceNorm_eq] using h

/-- Actual complex matrix of the compression of the *bounded
infinite-dimensional operator* to its first N Hilbert basis vectors. -/
def compressed (D : Data) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (b i.val) (boundedDiagonal D (b j.val))

theorem compressed_eq_diagonal (D : Data) (N : ℕ) :
    compressed D N =
      Matrix.diagonal (fun i : Fin N => (D.coeff i.val : ℂ)) := by
  ext i j
  change inner ℂ (b i.val) (boundedDiagonal D (b j.val)) =
    Matrix.diagonal (fun k : Fin N => (D.coeff k.val : ℂ)) i j
  rw [boundedDiagonal_eigen D j.val, inner_smul_right]
  by_cases hij : i = j
  · subst j
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i.val]
  · have hv : i.val ≠ j.val := by
      intro heq
      exact hij (Fin.ext heq)
    rw [b.orthonormal.inner_eq_zero hv]
    simp [Matrix.diagonal_apply, hij]

def finiteShift (D : Data) (N : ℕ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 + (t : ℂ) • compressed D N

theorem finiteShift_eq_diagonal (D : Data) (N : ℕ) (t : ℝ) :
    finiteShift D N t =
      Matrix.diagonal (fun i : Fin N =>
        1 + (t : ℂ) * (D.coeff i.val : ℂ)) := by
  rw [finiteShift, compressed_eq_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, smul_eq_mul]
  · simp [Matrix.diagonal_apply, hij]

theorem finiteShift_det (D : Data) (N : ℕ) (t : ℝ) :
    Matrix.det (finiteShift D N t) =
      ∏ i : Fin N, (1 + (t : ℂ) * (D.coeff i.val : ℂ)) := by
  rw [finiteShift_eq_diagonal, Matrix.det_diagonal]

theorem finiteShift_det_eq_real (D : Data) (N : ℕ) (t : ℝ) :
    Matrix.det (finiteShift D N t) =
      ((∏ n ∈ Finset.range N, (1 + t * D.coeff n) : ℝ) : ℂ) := by
  rw [finiteShift_det]
  calc
    (∏ i : Fin N, (1 + (t : ℂ) * (D.coeff i.val : ℂ))) =
        ∏ i : Fin N, ((1 + t * D.coeff i.val : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      push_cast
      ring
    _ = ((∏ i : Fin N, (1 + t * D.coeff i.val : ℝ)) : ℂ) := by
      simp only [Complex.ofReal_prod]
    _ = ((∏ n ∈ Finset.range N, (1 + t * D.coeff n) : ℝ) : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ))
        ((Finset.prod_range (n := N) (fun n : ℕ => 1 + t * D.coeff n)).symm)

/-- Infinite Fredholm product on the entire positive summable
diagonal sector; it is not defined through the Dirichlet spectrum. -/
def determinant (D : Data) (t : ℝ) : ℝ :=
  ∏' n : ℕ, (1 + t * D.coeff n)

theorem multipliable_factor (D : Data) (t : ℝ) :
    Multipliable (fun n : ℕ => 1 + t * D.coeff n) :=
  Real.multipliable_one_add_of_summable (D.summable.mul_left t)

/-- Determinants of genuine finite Hilbert-space compressions
converge to the sector determinant for EVERY positive summable
diagonal, not only for the Dirichlet special case. -/
theorem finiteShift_det_tendsto (D : Data) (t : ℝ) :
    Tendsto (fun N : ℕ => Matrix.det (finiteShift D N t))
      atTop (𝓝 ((determinant D t : ℝ) : ℂ)) := by
  have hreal :
      Tendsto (fun N : ℕ =>
        ∏ n ∈ Finset.range N, (1 + t * D.coeff n))
        atTop (𝓝 (determinant D t)) :=
    ((multipliable_factor D t).hasProd_iff_tendsto_nat).mp
      (multipliable_factor D t).hasProd
  have hcomplex :=
    (Complex.continuous_ofReal.tendsto (determinant D t)).comp hreal
  convert hcomplex using 1
  funext N
  exact finiteShift_det_eq_real D N t

/-- The already-certified Dirichlet spectral inverse is one member
of this genuine operatorial positive diagonal S₁ construction. -/
def dirichlet : Data where
  coeff := σ
  nonneg n := (σ_pos n).le
  summable := σ_summable

theorem dirichlet_boundedDiagonal_eq_inverse :
    boundedDiagonal dirichlet = inverse := rfl

theorem dirichlet_S1Diagonal_eq_inverse :
    (S1Diagonal dirichlet).1 = inverse := by
  rw [S1Diagonal_operator_eq, dirichlet_boundedDiagonal_eq_inverse]

theorem dirichlet_finiteShift_eq_existing (N : ℕ) (t : ℝ) :
    finiteShift dirichlet N t =
      Manuscript14Priority3.OperatorCompression.finiteOperatorShift N t := by
  rfl

#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.term_traceNorm_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.S1term_norm_summable
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.S1Diagonal_operator_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.S1Diagonal_traceNorm_eq
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.S1Diagonal_error_le_tail
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.compressed_eq_diagonal
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.finiteShift_det
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.finiteShift_det_eq_real
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.finiteShift_det_tendsto
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.dirichlet_S1Diagonal_eq_inverse
#print axioms Manuscript14Priority3.PositiveDiagonalFredholm.dirichlet_finiteShift_eq_existing

end Manuscript14Priority3.PositiveDiagonalFredholm
