import Manuscript15.CoefficientRigidity
import Mathlib

/-!
# Manuscript 15 — strict all-order alternation of the cycloidal recurrence coefficients

The exact conditional two-scale recurrence in Manuscript15.CoefficientRigidity
forces more than a finite list of rational Taylor coefficients.  Under
the hypothesis CoefficientRule c (which includes c(0)=1), ALL signed
coefficients have positive alternating sign:

  ∀ n : ℕ, 0 < (-1)^n c(n).

Proof: strong induction on n.  The rule at n expresses the signed
coefficient at n+1 as a positive scalar times a finite sum of products
of lower signed coefficients.  The n=0 seed equals 1.  Thus the
inductively positive convolution proves strict positivity at every order.

This is a *conditional* exact formal consequence of CoefficientRule;
it does not establish the analytic coefficient-extraction theorem or
the probabilistic uniqueness theorem for characteristic functions.
No floating-point calculations or positivity assumptions on c are made.
-/

noncomputable section
namespace Manuscript15

/-- All coefficients of the conditional two-scale cycloidal rigidity
recurrence have a strictly positive alternating sign after multiplying
by (-1)^n. This is an ALL-ORDER theorem, not finite computation. -/
theorem coefficientRule_all_orders_strict_alternation
    (c : ℕ → ℝ) (hc : CoefficientRule c) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        simp [hc.1]
    | succ k =>
        let D : ℝ := (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1))
        have hD : 0 < D := by
          dsimp [D]
          positivity
        have hrec : D * c (k + 1) =
            -((1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (k + 1), c j * c (k - j)) := hc.2 k
        have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
            0 < (-1 : ℝ) ^ k * (c j * c (k - j)) := by
          have hjle : j ≤ k := by
            have hjlt := Finset.mem_range.mp hj
            omega
          have hadd : j + (k - j) = k := Nat.add_sub_of_le hjle
          have heq :
              (-1 : ℝ) ^ k * (c j * c (k - j)) =
                ((-1 : ℝ) ^ j * c j) *
                  ((-1 : ℝ) ^ (k - j) * c (k - j)) := by
            calc
              (-1 : ℝ) ^ k * (c j * c (k - j)) =
                  ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (k - j)) *
                    (c j * c (k - j)) := by
                rw [← pow_add, hadd]
              _ = ((-1 : ℝ) ^ j * c j) *
                    ((-1 : ℝ) ^ (k - j) * c (k - j)) := by ring
          rw [heq]
          exact mul_pos (ih j (by omega)) (ih (k - j) (by omega))
        have hsum :
            0 < ∑ j ∈ Finset.range (k + 1),
              (-1 : ℝ) ^ k * (c j * c (k - j)) := by
          apply Finset.sum_pos
          · intro j hj
            exact hterm j hj
          · simp
        have hscaled :
            D * ((-1 : ℝ) ^ (k + 1) * c (k + 1)) =
              (1 / 2 : ℝ) * ∑ j ∈ Finset.range (k + 1),
                (-1 : ℝ) ^ k * (c j * c (k - j)) := by
          calc
            D * ((-1 : ℝ) ^ (k + 1) * c (k + 1)) =
                -((-1 : ℝ) ^ k) * (D * c (k + 1)) := by
                  rw [pow_succ]
                  ring
            _ = -((-1 : ℝ) ^ k) *
                  (-((1 / 2 : ℝ) *
                    ∑ j ∈ Finset.range (k + 1), c j * c (k - j))) := by
                  rw [hrec]
            _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.range (k + 1),
                  (-1 : ℝ) ^ k * (c j * c (k - j)) := by
                  rw [← Finset.mul_sum]
                  ring
        have hproduct : 0 < D *
            ((-1 : ℝ) ^ (k + 1) * c (k + 1)) := by
          rw [hscaled]
          exact mul_pos (by norm_num) hsum
        exact (mul_pos_iff_of_pos_left hD).mp hproduct

/-- Every coefficient of a solution to CoefficientRule is nonzero,
without a finite-index restriction or unproved nonvanishing claim. -/
theorem coefficientRule_all_orders_ne_zero
    (c : ℕ → ℝ) (hc : CoefficientRule c) (n : ℕ) :
    c n ≠ 0 := by
  intro hzero
  have hs := coefficientRule_all_orders_strict_alternation c hc n
  rw [hzero, mul_zero] at hs
  exact (lt_irrefl (0 : ℝ)) hs

#print axioms Manuscript15.coefficientRule_all_orders_strict_alternation
#print axioms Manuscript15.coefficientRule_all_orders_ne_zero

end Manuscript15
