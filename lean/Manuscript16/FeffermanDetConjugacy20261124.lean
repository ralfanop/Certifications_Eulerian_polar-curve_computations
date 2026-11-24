import Mathlib

/-!
M16 (24 Nov 2026), §2.3, label eq:feff-det.
Actual finite-dimensional regularized determinant under similarity, and
uniqueness of a common limit. This does NOT construct the infinite-dimensional
Schatten ideal, approximation convergence, or the geometric transport P.
-/

namespace Manuscript16.FeffermanDetConjugacy20261124

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℂ

theorem similarity_power (P Q A : Mat) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (n : ℕ) :
    (P * A * Q)^n = P * A^n * Q := by
  induction n with
  | zero => simpa using hPQ.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      P * A^n * Q * (P * A * Q) =
          P * A^n * (Q * P) * A * Q := by noncomm_ring
      _ = P * (A^n * A) * Q := by simp [hQP, mul_assoc]

theorem similarity_trace (P Q A : Mat) (hQP : Q * P = 1) :
    Matrix.trace (P * A * Q) = Matrix.trace A := by
  calc
    Matrix.trace (P * A * Q) = Matrix.trace (Q * (P * A)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace A := by rw [← mul_assoc, hQP, one_mul]

theorem similarity_trace_power (P Q A : Mat) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (n : ℕ) :
    Matrix.trace ((P * A * Q)^n) = Matrix.trace (A^n) := by
  rw [similarity_power P Q A hPQ hQP, similarity_trace P Q (A^n) hQP]

theorem similarity_det (P Q A : Mat) (hPQ : P * Q = 1) :
    Matrix.det (P * A * Q) = Matrix.det A := by
  have h : Matrix.det P * Matrix.det Q = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det P * Matrix.det A * Matrix.det Q =
        Matrix.det A * (Matrix.det P * Matrix.det Q) := by ring
    _ = Matrix.det A := by rw [h, mul_one]

theorem similarity_shifted_det (P Q A : Mat) (hPQ : P * Q = 1) :
    Matrix.det (1 + P * A * Q) = Matrix.det (1 + A) := by
  have h : P * (1 + A) * Q = 1 + P * A * Q := by
    rw [mul_add, add_mul, mul_one, hPQ]
  rw [← h, similarity_det P Q (1 + A) hPQ]

/-- Finite regularized determinant, with A = zT.
    For p ≥ 1, the exponential correction sums k=1,...,p-1. -/
noncomputable def regDet (p : ℕ) (A : Mat) : ℂ :=
  Matrix.det (1 + A) *
    Complex.exp (∑ j ∈ Finset.range (p - 1),
      ((-1 : ℂ)^(j+1) / ((j+1 : ℕ) : ℂ)) * Matrix.trace (A^(j+1)))

theorem similarity_regDet (p : ℕ) (P Q A : Mat) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) :
    regDet p (P * A * Q) = regDet p A := by
  unfold regDet
  rw [similarity_shifted_det P Q A hPQ]
  have h : (∑ j ∈ Finset.range (p - 1),
      ((-1 : ℂ)^(j+1) / ((j+1 : ℕ) : ℂ)) *
        Matrix.trace ((P * A * Q)^(j+1))) =
      ∑ j ∈ Finset.range (p - 1),
      ((-1 : ℂ)^(j+1) / ((j+1 : ℕ) : ℂ)) *
        Matrix.trace (A^(j+1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [similarity_trace_power P Q A hPQ hQP]
  rw [h]

/-- If finite-rank approximations yield convergent regularized determinants,
    similarity preserves the limit. Existence of those approximations and
    convergence in the Schatten topology are separate obligations. -/
theorem similarity_regDet_limit (p : ℕ) (A P Q : ℕ → Mat)
    (hPQ : ∀ n, P n * Q n = 1) (hQP : ∀ n, Q n * P n = 1)
    (a b : ℂ)
    (ha : Filter.Tendsto (fun n => regDet p (A n)) Filter.atTop (nhds a))
    (hb : Filter.Tendsto (fun n => regDet p (P n * A n * Q n))
      Filter.atTop (nhds b)) : a = b := by
  have h : (fun n => regDet p (P n * A n * Q n)) =
      (fun n => regDet p (A n)) := by
    funext n
    exact similarity_regDet p (P n) (Q n) (A n) (hPQ n) (hQP n)
  rw [h] at hb
  exact tendsto_nhds_unique ha hb

#print axioms similarity_power
#print axioms similarity_trace
#print axioms similarity_trace_power
#print axioms similarity_det
#print axioms similarity_shifted_det
#print axioms similarity_regDet
#print axioms similarity_regDet_limit

end Manuscript16.FeffermanDetConjugacy20261124
