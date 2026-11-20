import Mathlib

/-! M12 Section 9: algebraic prerequisites for the quartic critical window.
The genuine analytic Fock-integral limit is a subsequent milestone. -/
namespace M12CriticalWindow

theorem standardized_fourth_cumulant :
    (9 / 5 : ℝ) - 3 * 1 ^ 2 = -6 / 5 := by norm_num

theorem logarithmic_fourth_coefficient :
    (3 / 40 : ℝ) - (1 / 2) ^ 2 / 2 = -1 / 20 := by norm_num

theorem factorial_step (n : ℕ) :
    6 * (n + 1) ≤ (2 * n + 2) * (2 * n + 3) := by
  nlinarith

theorem factorial_comparison (n : ℕ) :
    6 ^ n * n.factorial ≤ (2 * n + 1).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hstep := factorial_step n
    have h : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [h, Nat.factorial_succ, Nat.factorial_succ, pow_succ, Nat.factorial_succ]
    calc
      6 ^ n * 6 * ((n + 1) * n.factorial) =
          (6 * (n + 1)) * (6 ^ n * n.factorial) := by ring
      _ ≤ ((2 * n + 2) * (2 * n + 3)) * (2 * n + 1).factorial :=
        Nat.mul_le_mul hstep ih
      _ = (2 * n + 1 + 1 + 1) * ((2 * n + 1 + 1) * (2 * n + 1).factorial) := by ring

theorem strict_quartic_series_gap :
    (1 / 8 : ℝ) - 3 / 40 = 1 / 20 := by norm_num

/-- ε = M^(-1/4). This is the exact Taylor-polynomial cancellation
before multiplying by M = ε^(-4). -/
theorem critical_exponent_normal_form (ε lam u w : ℝ) :
    2 * ((u^2 * ε^2 - w^2 * ε^4) / 4 -
        (u^4 * ε^4 - 6*u^2*w^2*ε^6 + w^4*ε^8) / 80) -
       6 * (1/12 + lam*ε^2) * (u^2*ε^2 + w^2*ε^4)
    = ε^4 * (-w^2 - u^4/40 - 6*lam*u^2) +
      ε^6 * (3/20*u^2*w^2 - 6*lam*w^2) - ε^8*w^4/40 := by
  ring

theorem outer_region_bound (b s L u : ℝ) (h : 6*L+1 ≤ b*s) :
    6*L*u^2-b*s*u^2 ≤ -u^2 := by
  have h' := mul_le_mul_of_nonneg_right h (sq_nonneg u)
  nlinarith only [h']

theorem quartic_gaussian_domination (b L u : ℝ) (hb : 0 < b)
    (hu : 4*(6*L+1) ≤ b*u^2) :
    6*L*u^2 - b*u^4/2 ≤ -u^2 := by
  have h' := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
  have hp : 0 ≤ b*u^4 := mul_nonneg hb.le (by positivity)
  nlinarith only [h', hp]

end M12CriticalWindow

#print axioms M12CriticalWindow.standardized_fourth_cumulant
#print axioms M12CriticalWindow.logarithmic_fourth_coefficient
#print axioms M12CriticalWindow.factorial_step
#print axioms M12CriticalWindow.factorial_comparison
#print axioms M12CriticalWindow.strict_quartic_series_gap
#print axioms M12CriticalWindow.critical_exponent_normal_form
#print axioms M12CriticalWindow.outer_region_bound
#print axioms M12CriticalWindow.quartic_gaussian_domination
