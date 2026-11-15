import Mathlib

/-!
M15, Internal-Hyperlinks revision (2026-11-15).
Exact leading-coefficient ratio and all-order Gaussian moment weights.
This does not identify the analytic Lagrange inverse, prime continuation,
or all-order asymptotic remainder.
-/

noncomputable section

namespace Manuscript15.InternalHyperlinks20261115

def terminalCoefficient (M : ℕ) : ℝ :=
  1 / (2 * (4 * Real.pi ^ 2) ^ (M - 1))

theorem terminal_coefficient_ratio (M : ℕ) (hM : 2 ≤ M) :
    terminalCoefficient M / terminalCoefficient (M + 1) = 4 * Real.pi ^ 2 := by
  have h : M + 1 - 1 = (M - 1) + 1 := by omega
  have hp : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  unfold terminalCoefficient
  rw [h, pow_succ]
  field_simp [hp, pow_ne_zero _ hp] <;> ring

/-- The adjacent terminal ratio telescopes over any finite number of steps.
This is an exact identity, not an analytic asymptotic statement. -/
theorem terminal_coefficient_shift (M k : ℕ) (hM : 2 ≤ M) :
    terminalCoefficient M =
      (4 * Real.pi ^ 2) ^ k * terminalCoefficient (M + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpos : terminalCoefficient (M + k + 1) ≠ 0 := by
        unfold terminalCoefficient
        positivity
      have hr := terminal_coefficient_ratio (M + k) (by omega)
      have heq : terminalCoefficient (M + k) =
          (4 * Real.pi ^ 2) * terminalCoefficient (M + k + 1) :=
        (div_eq_iff hpos).mp hr
      calc
        terminalCoefficient M =
            (4 * Real.pi ^ 2) ^ k * terminalCoefficient (M + k) := ih
        _ = (4 * Real.pi ^ 2) ^ (k + 1) *
            terminalCoefficient (M + (k + 1)) := by
              rw [heq, pow_succ]
              push_cast
              ring

/-- The revised local numerator is exactly the previous expression. -/
theorem terminal_numerator_rewrite (M : ℕ) (hM : 1 ≤ M) (u : ℝ) :
    (2 * Real.sin (u / 2)) ^ (2 * M) /
      (2 * (2 * Real.pi + u) ^ (2 * M - 2)) =
      2 * Real.sin (u / 2) ^ (2 * M) /
        (Real.pi + u / 2) ^ (2 * M - 2) := by
  have h : 2 * M = (2 * M - 2) + 2 := by omega
  rw [show 2 * Real.pi + u = 2 * (Real.pi + u / 2) by ring, mul_pow, mul_pow]
  have hpow : (2 : ℝ) ^ (2 * M) =
      (2 : ℝ) ^ (2 * M - 2) * 4 := by
    conv_lhs => rw [h, pow_add]
    norm_num
  rw [hpow]
  by_cases hz : (Real.pi + u / 2) ^ (2 * M - 2) = 0
  · simp [hz]
  · field_simp [hz, pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

def gaussianWeight (r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r + 1) : ℝ) / 2 ^ r

theorem gaussian_weight_succ (r : ℕ) :
    gaussianWeight (r+1) = ((2 * (r : ℝ) + 3) / 2) * gaussianWeight r := by
  unfold gaussianWeight
  rw [show 2 * (r+1) + 1 = (2*r+1)+2 by omega,
    Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ]
  push_cast
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

/-- Strict positivity of every Gaussian moment weight. -/
theorem gaussian_weight_pos (r : ℕ) : 0 < gaussianWeight r := by
  unfold gaussianWeight
  positivity

/-- The normalized Gaussian weights increase strictly at every order.
This finite algebraic statement does not assert convergence of a moment
expansion or a uniform asymptotic remainder. -/
theorem gaussian_weight_strict_mono (r : ℕ) :
    gaussianWeight r < gaussianWeight (r + 1) := by
  rw [gaussian_weight_succ]
  have hp := gaussian_weight_pos r
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

/-- The normalized Gamma values giving the Gaussian weights. The improper
integral substitution is separately tracked in the scope ledger. -/
theorem gaussian_gamma_ratio (r : ℕ) :
    Real.Gamma ((r : ℝ) + 3/2) / Real.Gamma (3/2) = gaussianWeight r := by
  induction r with
  | zero =>
      have h : Real.Gamma (3/2 : ℝ) ≠ 0 := by positivity
      simp [gaussianWeight, h]
  | succ r ih =>
      have h : (r : ℝ) + 3/2 ≠ 0 := by positivity
      rw [Nat.cast_succ, show (r : ℝ) + 1 + 3/2 = ((r : ℝ) + 3/2) + 1 by ring,
        Real.Gamma_add_one h, gaussian_weight_succ, ← ih]
      ring

/-- Exact factorial identity for every normalized Gaussian weight, not
only the finitely many coefficients explicitly displayed in the manuscript. -/
theorem gaussian_weight_central_binomial (r : ℕ) :
    gaussianWeight r =
      ((2 * r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) * ((2*r).choose r : ℝ) / 4 ^ r := by
  have h1 : Nat.doubleFactorial (2*r+1) * (2^r * r.factorial) =
      (2*r+1) * (2*r).factorial := by
    rw [← Nat.doubleFactorial_two_mul, ← Nat.factorial_eq_mul_doubleFactorial, Nat.factorial_succ]
  have h2 : (2*r).choose r * r.factorial * r.factorial = (2*r).factorial := by
    simpa only [two_mul] using Nat.add_choose_mul_factorial_mul_factorial r r
  have h3 : (Nat.doubleFactorial (2*r+1) : ℝ) * ((2:ℝ)^r * (r.factorial : ℝ)) =
      ((2*r+1 : ℕ) : ℝ) * ((2*r).factorial : ℝ) := by exact_mod_cast h1
  have h4 : ((2*r).choose r : ℝ) * (r.factorial : ℝ) * (r.factorial : ℝ) =
      ((2*r).factorial : ℝ) := by exact_mod_cast h2
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  have h5 : (Nat.doubleFactorial (2*r+1) : ℝ) * (2:ℝ)^r =
      ((2*r+1 : ℕ) : ℝ) * (r.factorial : ℝ) * ((2*r).choose r : ℝ) := by
    apply mul_right_cancel₀ hf
    calc
      _ = (Nat.doubleFactorial (2*r+1) : ℝ) * ((2:ℝ)^r * (r.factorial : ℝ)) := by ring
      _ = ((2*r+1 : ℕ) : ℝ) * ((2*r).factorial : ℝ) := h3
      _ = _ := by rw [← h4]; ring
  unfold gaussianWeight
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [show (4:ℝ)^r = (2:ℝ)^r * (2:ℝ)^r by rw [← mul_pow]; norm_num]
  calc
    _ = ((Nat.doubleFactorial (2*r+1) : ℝ) * (2:ℝ)^r) * (2:ℝ)^r := by ring
    _ = _ := by rw [h5]

end Manuscript15.InternalHyperlinks20261115

#print axioms Manuscript15.InternalHyperlinks20261115.terminal_coefficient_ratio
#print axioms Manuscript15.InternalHyperlinks20261115.terminal_coefficient_shift
#print axioms Manuscript15.InternalHyperlinks20261115.terminal_numerator_rewrite
#print axioms Manuscript15.InternalHyperlinks20261115.gaussian_weight_succ
#print axioms Manuscript15.InternalHyperlinks20261115.gaussian_gamma_ratio
#print axioms Manuscript15.InternalHyperlinks20261115.gaussian_weight_central_binomial

#print axioms Manuscript15.InternalHyperlinks20261115.gaussian_weight_pos
#print axioms Manuscript15.InternalHyperlinks20261115.gaussian_weight_strict_mono
