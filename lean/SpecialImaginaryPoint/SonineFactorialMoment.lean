import Mathlib
import SpecialImaginaryPoint.SonineIntegralMoment

/-!
# Manuscript 14.1 §4 — exact factorial closed form of the Sonine moments

The original Sonine moment sequence is an exact rational recursion, and
`integralMoment_eq_moment` already establishes the genuine interval integral.
Here we prove, for ALL n : ℕ, the closed factorial expression

  (1/2) ∫_{-1}¹ (1-u²)^n du = 4^n (n!)² / (2n+1)!.

This proof is universal and kernel-checked, not a finite numerical regression.
-/

namespace Manuscript14Sonine

/-- Explicit rational moment, with integer factorials cast to ℚ. -/
def factorialMoment (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n * (Nat.factorial n : ℚ) ^ 2 /
    (Nat.factorial (2*n+1) : ℚ)

theorem factorialMoment_zero : factorialMoment 0 = 1 := by
  norm_num [factorialMoment]

private theorem factorialMoment_numerator_succ (n : ℕ) :
    ((Nat.factorial (n + 1) : ℕ) : ℚ) =
      ((n : ℚ) + 1) * (Nat.factorial n : ℚ) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

private theorem factorialMoment_denominator_succ (n : ℕ) :
    ((Nat.factorial (2 * n + 3) : ℕ) : ℚ) =
      (2 * (n : ℚ) + 3) * (2 * (n : ℚ) + 2) *
        (Nat.factorial (2*n+1) : ℚ) := by
  have hn : (2*n+3).factorial =
      (2*n+3) * (2*n+2) * (2*n+1).factorial := by
    rw [show 2*n+3 = (2*n+2)+1 by omega,
        Nat.factorial_succ,
        show 2*n+2 = (2*n+1)+1 by omega,
        Nat.factorial_succ]
    ring
  rw [hn]
  push_cast
  ring

theorem factorialMoment_succ (n : ℕ) :
    factorialMoment (n+1) =
      ((2 * (n : ℚ) + 2) / (2 * (n : ℚ) + 3)) * factorialMoment n := by
  have hden : (Nat.factorial (2*n+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*n+1)
  have h2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
  simp only [factorialMoment, pow_succ]
  rw [show 2 * (n+1) + 1 = 2*n+3 by omega,
      factorialMoment_numerator_succ,
      factorialMoment_denominator_succ]
  field_simp [hden, h2, h3]
  ring

/-- The genuine recurrence-defined Sonine coefficient has the closed form. -/
theorem moment_eq_factorialMoment (n : ℕ) :
    moment n = factorialMoment n := by
  induction n with
  | zero =>
      rw [moment_zero, factorialMoment_zero]
  | succ n ih =>
      rw [moment_step, factorialMoment_succ, ih]

/-- The printed integral formula, for all n, now proved in the Lean kernel. -/
theorem integralMoment_eq_factorial (n : ℕ) :
    integralMoment n =
      (4 : ℝ)^n * (Nat.factorial n : ℝ)^2 /
        (Nat.factorial (2*n+1) : ℝ) := by
  rw [integralMoment_eq_moment, moment_eq_factorialMoment]
  norm_num [factorialMoment]
  push_cast
  rfl

#print axioms Manuscript14Sonine.factorialMoment_succ
#print axioms Manuscript14Sonine.moment_eq_factorialMoment
#print axioms Manuscript14Sonine.integralMoment_eq_factorial

end Manuscript14Sonine
