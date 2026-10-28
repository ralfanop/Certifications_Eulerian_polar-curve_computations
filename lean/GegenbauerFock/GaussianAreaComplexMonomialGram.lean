import GegenbauerFock.GaussianAreaNormalizedMonomialGram
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# V007 — exact complex Gaussian-area Gram matrix for monomials

The previously established off-diagonal orthogonality and real
squared-norm integrals are consolidated as a genuine complex-valued
Gram integral for every pair of monomials.  In particular the diagonal
complex integral is proved by commuting the real-to-complex embedding
with the Bochner integral, not by assuming the desired normalization.

The result is a prerequisite for the Gaussian holomorphic L² Fock
realization.  The full L² realization, polynomial density, and onto
isometry are separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The diagonal complex Gaussian-area integral is the genuine real
Gaussian monomial squared norm, with the exact factorial weight. -/
theorem integral_normalized_complex_monomial_diagonal
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ n * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      (((Nat.factorial n : ℝ) * alpha ^ (-(n : ℝ))) : ℂ) := by
  calc
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ n * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      (∫ z : ℂ,
        (((alpha / Real.pi) *
          (‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2))) : ℝ) : ℂ) := by
        congr 1
        funext z
        rw [Complex.star_def, Complex.mul_conj']
        push_cast
        ring
    _ = (((∫ z : ℂ,
        (alpha / Real.pi) *
          (‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2))) : ℝ) : ℂ) :=
          integral_complex_ofReal
    _ = _ := congrArg (fun x : ℝ => (x : ℂ))
      (integral_normalized_monomial_norm_sq alpha ha n)

/-- Every entry of the full (not truncated) monomial Gram matrix,
computed using the normalized two-dimensional complex Gaussian area. -/
theorem integral_normalized_complex_monomial_gram
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ m * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      if m = n then
        (((Nat.factorial m : ℝ) * alpha ^ (-(m : ℝ))) : ℂ)
      else 0 := by
  by_cases h : m = n
  · subst n
    simpa using integral_normalized_complex_monomial_diagonal alpha ha m
  · simp only [if_neg h]
    exact normalized_gaussian_mixed_monomial_eq_zero alpha ha m n h

/-- Diagonal Gaussian monomial Gram entries are strictly positive,
and hence the diagonal complex Gram values do not vanish. -/
theorem integral_normalized_complex_monomial_diagonal_ne_zero
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ n * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) ≠ 0 := by
  rw [integral_normalized_complex_monomial_diagonal alpha ha n]
  exact_mod_cast (ne_of_gt (mul_pos
    (by exact_mod_cast Nat.factorial_pos n)
    (Real.rpow_pos_of_pos ha _)))

#print axioms GegenbauerFock.GaussianArea.integral_normalized_complex_monomial_diagonal
#print axioms GegenbauerFock.GaussianArea.integral_normalized_complex_monomial_gram
#print axioms GegenbauerFock.GaussianArea.integral_normalized_complex_monomial_diagonal_ne_zero

end GegenbauerFock.GaussianArea
