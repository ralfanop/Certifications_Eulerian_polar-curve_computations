import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace EulerianGrothendieck

/-- A finite algebraic remainder estimate. Its hypotheses are dimensionless bounds,
not assumptions of the Fock asymptotic theorem. -/
theorem squared_moment_remainder (r x e : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : 0 ≤ x)
    (he0 : 0 ≤ r - (1 - x)) (he : r - (1 - x) ≤ e) :
    0 ≤ r ^ 2 - (1 - 2 * x) ∧ r ^ 2 - (1 - 2 * x) ≤ x ^ 2 + 2 * e := by
  have hsq : (1 - r) ^ 2 ≤ x ^ 2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (1 - r)]

theorem falling_factorial_identity (k : ℝ) :
    k ^ 2 * (k - 1) ^ 2 =
      k * (k - 1) * (k - 2) * (k - 3) +
      4 * k * (k - 1) * (k - 2) + 2 * k * (k - 1) := by ring

theorem moment_remainder_constant (k : ℝ) :
    (k * (k - 1) / 5) ^ 2 + 2 * (k * (k - 1) / 2) ^ 2 =
      (27 / 50 : ℝ) * k ^ 2 * (k - 1) ^ 2 := by ring

theorem inverse_second_order_identity (F N : ℝ) (hF : F ≠ 0) (hN : N ≠ 0) :
    1 / N = 1 / F + (F - N) / F ^ 2 + (F - N) ^ 2 / (F ^ 2 * N) := by
  field_simp
  <;> ring

theorem inverse_remainder_identity (F N A E M : ℝ)
    (hF : F ≠ 0) (hN : N ≠ 0) (hM : M ≠ 0)
    (h : N = F - A / M + E / M ^ 2) :
    1 / N - (1 / F + A / (F ^ 2 * M)) =
       -E / (F ^ 2 * M ^ 2) + (F - N) ^ 2 / (F ^ 2 * N) := by
  rw [inverse_second_order_identity F N hF hN]
  have heq : F - N = A / M - E / M ^ 2 := by linarith
  rw [heq]
  field_simp
  <;> ring

theorem global_quadratic_minimum (u v c d : ℝ) :
    u ^ 2 + v ^ 2 + (v + c) ^ 2 + (v + d) ^ 2 =
      u ^ 2 + 3 * (v + (c + d) / 3) ^ 2 + c ^ 2 + d ^ 2 - (c + d) ^ 2 / 3 := by ring

theorem global_quadratic_lower_bound (u v c d : ℝ) :
    c ^ 2 + d ^ 2 - (c + d) ^ 2 / 3 ≤
      u ^ 2 + v ^ 2 + (v + c) ^ 2 + (v + d) ^ 2 := by
  rw [global_quadratic_minimum]
  nlinarith [sq_nonneg u, sq_nonneg (v + (c + d) / 3)]

theorem tilted_hermite_identity (t : ℝ) (ht : 1-t^2 ≠ 0) :
    3 / (1-t^2)^2 - 6 / (1-t^2) + 3 = 3*t^4 / (1-t^2)^2 := by
  field_simp
  <;> ring

end EulerianGrothendieck

