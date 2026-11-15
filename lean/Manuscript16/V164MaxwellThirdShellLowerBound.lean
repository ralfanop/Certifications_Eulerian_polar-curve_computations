/- Manuscript 16 v16.4, Proposition 13, necessary Schatten threshold.
   Scalar nearest-temporal-mode estimate at p=3. This is NOT the
   analytic proof of divergence nor the operator Schatten theorem. -/
import Mathlib

namespace Manuscript16

/-- For spatial index ell >= 2, the nearest nonresonant Maxwell mode
    m=ell+2 has absolute wave eigenvalue 4*(ell+1). -/
theorem v164_maxwell_nearest_mode (ell : ℤ) :
    ell ^ 2 - (ell + 2) ^ 2 = -4 * (ell + 1) := by
  ring

/-- The multiplicity-weighted nearest-mode third-power summand
    dominates a fixed shifted harmonic summand. -/
theorem v164_maxwell_third_shell_ge_harmonic (ell : ℕ) (h : 2 ≤ ell) :
    1 / (96 * ((ell : ℝ) + 1)) ≤
      2 * (((ell : ℝ) ^ 2) - 1) /
        ((4 * ((ell : ℝ) + 1)) ^ 3) := by
  have hx : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast h
  have hp : 0 < (ell : ℝ) + 1 := by linarith
  have hprod : 0 ≤ (((ell : ℝ) + 1) ^ 2) * ((ell : ℝ) - 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [hprod]

#print axioms Manuscript16.v164_maxwell_nearest_mode
#print axioms Manuscript16.v164_maxwell_third_shell_ge_harmonic
end Manuscript16
