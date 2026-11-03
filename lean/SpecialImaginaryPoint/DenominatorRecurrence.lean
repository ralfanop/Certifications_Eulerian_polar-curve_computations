import Mathlib

/-!
# Special Eulerian point i/sqrt(2): exact denominator recurrence

For the special-value expansion

  r_E(i/sqrt(2)) = sum_{n >= 0} 1 / (8^n (2n+1)!),

this module certifies the integer denominator recurrence and its first
five values.  It does not claim to formalize convergence or the analytic
identity with the hyperbolic sine; those are separate obligations.

The module is isolated from existing manuscripts V097 and V007.
-/

namespace EulerianSpecialPoint

/-- Exact positive integer denominator of the n-th Eulerian special-value term. -/
def denominator (n : ℕ) : ℕ := 8 ^ n * (2 * n + 1).factorial

theorem denominator_zero : denominator 0 = 1 := by
  norm_num [denominator]

theorem denominator_succ (n : ℕ) :
    denominator (n + 1) =
      8 * (2 * n + 2) * (2 * n + 3) * denominator n := by
  unfold denominator
  have hindex : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
  rw [hindex, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  ring

theorem denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  positivity

theorem denominator_first_five :
    denominator 0 = 1 ∧
    denominator 1 = 48 ∧
    denominator 2 = 7680 ∧
    denominator 3 = 2580480 ∧
    denominator 4 = 1486356480 := by
  norm_num [denominator]

#print axioms EulerianSpecialPoint.denominator_zero
#print axioms EulerianSpecialPoint.denominator_succ
#print axioms EulerianSpecialPoint.denominator_pos
#print axioms EulerianSpecialPoint.denominator_first_five

end EulerianSpecialPoint
