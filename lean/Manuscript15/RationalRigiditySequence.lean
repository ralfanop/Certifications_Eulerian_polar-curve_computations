import Manuscript15.CoefficientExistence
import Mathlib

/-!
# Manuscript 15 — rationality of every coefficient in the canonical all-order rigidity sequence

The exact two-scale triangular cycloidal recurrence has a unique REAL
algebraic coefficient sequence c_n (CoefficientExistence). This
module constructs the SAME recurrence by well-founded recursion over
the RATIONAL field and proves, by exact strong induction and coercion,
that the real canonical sequence is its scalar extension from ℚ.

Hence for EVERY natural-number index n the coefficient c_n is
an exact rational number, not just the finitely tabulated c_1...c_13.
No floating-point assumptions, analytic-convergence assertions or
probabilistic existence claims are made.
-/

noncomputable section

namespace Manuscript15

/-- All-order two-scale recurrence constructed directly over ℚ. -/
noncomputable def rationalRigidityCoefficientSequence (n : ℕ) : ℚ :=
  Nat.strongRecOn n (fun n ih =>
    match n with
    | 0 => 1
    | k + 1 =>
        -((1 / 2 : ℚ) *
          ∑ j : (Finset.range (k + 1)),
            ih j.1 (by have hj := Finset.mem_range.mp j.2; omega) *
              ih (k - j.1) (by omega)) /
          ((((2 * (k + 1) + 1 : ℕ) : ℚ) * (4 : ℚ) ^ (k + 1))))

/-- Exact rational initial value of the complete recurrence. -/
theorem rationalRigidityCoefficientSequence_zero :
    rationalRigidityCoefficientSequence 0 = 1 := by
  unfold rationalRigidityCoefficientSequence
  rw [Nat.strongRecOn_eq]

/-- Exact rational quadratic recursion at every positive coefficient. -/
theorem rationalRigidityCoefficientSequence_succ (n : ℕ) :
    rationalRigidityCoefficientSequence (n + 1) =
      -((1 / 2 : ℚ) *
        ∑ j ∈ Finset.range (n + 1),
          rationalRigidityCoefficientSequence j *
            rationalRigidityCoefficientSequence (n - j)) /
        ((((2 * (n + 1) + 1 : ℕ) : ℚ) * (4 : ℚ) ^ (n + 1))) := by
  conv_lhs =>
    rw [rationalRigidityCoefficientSequence, Nat.strongRecOn_eq]
  rw [← Finset.sum_attach]
  rfl

/-- The real canonical coefficients are exactly rational coefficient
casts at ALL orders, with no analytic approximation. -/
theorem rationalRigidityCoefficientSequence_cast_eq (n : ℕ) :
    ((rationalRigidityCoefficientSequence n : ℚ) : ℝ) =
      rigidityCoefficientSequence n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        simp [rationalRigidityCoefficientSequence_zero,
          rigidityCoefficientSequence_zero]
    | succ k =>
        have heq :
            (∑ j ∈ Finset.range (k + 1),
              ((rationalRigidityCoefficientSequence j : ℚ) : ℝ) *
                ((rationalRigidityCoefficientSequence (k - j) : ℚ) : ℝ)) =
            ∑ j ∈ Finset.range (k + 1),
              rigidityCoefficientSequence j *
                rigidityCoefficientSequence (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j (by omega), ih (k - j) (by omega)]
        calc
          ((rationalRigidityCoefficientSequence (k + 1) : ℚ) : ℝ) =
              -((1 / 2 : ℝ) *
                ∑ j ∈ Finset.range (k + 1),
                  ((rationalRigidityCoefficientSequence j : ℚ) : ℝ) *
                    ((rationalRigidityCoefficientSequence (k - j) : ℚ) : ℝ)) /
                ((((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1))) := by
              rw [rationalRigidityCoefficientSequence_succ]
              push_cast
              ring
          _ = rigidityCoefficientSequence (k + 1) := by
              rw [rigidityCoefficientSequence_succ, heq]

/-- Every coefficient of the UNIQUE canonical all-order cycloidal
rigidity recurrence is literally a rational number embedded in ℝ. -/
theorem rigidityCoefficientSequence_all_rational (n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = rigidityCoefficientSequence n :=
  ⟨rationalRigidityCoefficientSequence n,
    rationalRigidityCoefficientSequence_cast_eq n⟩

#print axioms Manuscript15.rationalRigidityCoefficientSequence_zero
#print axioms Manuscript15.rationalRigidityCoefficientSequence_succ
#print axioms Manuscript15.rationalRigidityCoefficientSequence_cast_eq
#print axioms Manuscript15.rigidityCoefficientSequence_all_rational

end Manuscript15
