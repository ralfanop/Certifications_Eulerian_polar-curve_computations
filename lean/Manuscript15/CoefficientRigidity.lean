/-
Manuscript 15 — coefficient uniqueness, 10 November 2026.

For an even entire characteristic function f(t) = sum c_n t^(2n),
the differential equation
  1 - f(2t) - 2t f'(2t) = t² f(t)²/2
formally yields
  (2n+3) 4^(n+1) c_(n+1) =
    - (1/2) sum_(j=0)^n c_j c_(n-j).

This module proves uniqueness of a sequence satisfying this recurrence and c_0=1.
Extraction of the recurrence from analytic Taylor coefficients, and the
characteristic-function uniqueness theorem, are NOT certified in this module.
-/
import Mathlib

namespace Manuscript15

/-- The exact recurrence extracted from the proposed cycloidal kinematics,
written using n+1 so all coefficients on the right have smaller index. -/
def CoefficientRule (c : ℕ → ℝ) : Prop :=
  c 0 = 1 ∧
    ∀ n : ℕ,
      (((2 * (n + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1)) * c (n + 1) =
        - ((1 / 2 : ℝ) * ∑ j ∈ Finset.range (n + 1), c j * c (n - j))

/-- Once c_0=1, the cycloidal coefficient recurrence has at most one solution. -/
theorem coefficientRule_unique (c d : ℕ → ℝ)
    (hc : CoefficientRule c) (hd : CoefficientRule d) : c = d := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact hc.1.trans hd.1.symm
    | succ k =>
      have hsum :
          (∑ j ∈ Finset.range (k + 1), c j * c (k - j)) =
          (∑ j ∈ Finset.range (k + 1), d j * d (k - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < k + 1 := Finset.mem_range.mp hj
        have hleft : c j = d j := ih j (by omega)
        have hright : c (k - j) = d (k - j) := ih (k - j) (by omega)
        rw [hleft, hright]
      have hfactor :
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) ≠ 0 := by
        positivity
      have heq :
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) * c (k + 1) =
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) * d (k + 1) := by
        calc
          _ = - ((1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (k + 1), c j * c (k - j)) := hc.2 k
          _ = - ((1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (k + 1), d j * d (k - j)) := by rw [hsum]
          _ = _ := (hd.2 k).symm
      exact (mul_left_cancel₀ hfactor) heq

#print axioms Manuscript15.coefficientRule_unique

end Manuscript15
