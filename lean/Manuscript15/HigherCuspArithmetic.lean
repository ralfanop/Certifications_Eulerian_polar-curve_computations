/-
Manuscript 15 — formal arithmetic core of the fourth-moment cusp and
convolution-hierarchy formulas. Exact polynomial identities only.

No analytic limits, asymptotic error estimates, or probabilistic
moment existence are asserted or imported into these theorems.
-/
import Mathlib

noncomputable section
namespace Manuscript15

/-- In the centred-uniform convolution model, the fourth-moment
    arithmetic coming from independent summands simplifies to the
    polynomial displayed in the manuscript. The combinatorial/probability
    derivation of the first expression is a separate obligation. -/
theorem uniform_sum_fourth_moment_arithmetic (M : ℝ) :
    M / 80 + 6 * (M * (M - 1) / 2) * (1 / 12 : ℝ) ^ 2 =
      (5 * M ^ 2 - 2 * M) / 240 := by
  ring

/-- The leading normalized cusp quotient after substituting
    sigma_M² = M/12; the proof is purely algebraic. -/
theorem uniform_sum_leading_cusp_arithmetic (M a : ℝ) :
    32 * (M / 12) ^ 2 / a = 2 * M ^ 2 / (9 * a) := by
  ring

/-- Algebraic substitution of sigma_M² and m4_M into the universal
    fourth-moment correction 3 sigma² - 2 m4/(3 sigma²). -/
theorem uniform_sum_quadratic_cusp_arithmetic (M : ℝ) (hM : M ≠ 0) :
    3 * (M / 12) -
      2 * ((5 * M ^ 2 - 2 * M) / 240) / (3 * (M / 12)) =
        (5 * M + 4) / 60 := by
  field_simp [hM]
  <;> ring

/-- Inversion of the quadratic cusp-correction coefficient: if
    b = 3 sigma² - 2 m4/(3 sigma²), then the fourth moment is
    algebraically determined for nonzero variance. -/
theorem fourth_moment_recovery_arithmetic (sigma2 m4 b : ℝ)
    (hs : sigma2 ≠ 0)
    (hb : b = 3 * sigma2 - 2 * m4 / (3 * sigma2)) :
    m4 = (3 * sigma2 / 2) * (3 * sigma2 - b) := by
  rw [hb]
  field_simp [hs]
  <;> ring

#print axioms Manuscript15.uniform_sum_fourth_moment_arithmetic
#print axioms Manuscript15.uniform_sum_leading_cusp_arithmetic
#print axioms Manuscript15.uniform_sum_quadratic_cusp_arithmetic
#print axioms Manuscript15.fourth_moment_recovery_arithmetic

end Manuscript15
