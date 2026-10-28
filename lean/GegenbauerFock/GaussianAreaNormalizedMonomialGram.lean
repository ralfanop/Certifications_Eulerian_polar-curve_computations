import GegenbauerFock.GaussianAreaFullMonomialOrthogonality

/-!
# V007 — normalized Gaussian-area Gram data of monomials

The normalized Gaussian area measure has density α/π·exp(-α‖z‖²)
for α>0. These are exact off-diagonal zeroes and the diagonal
factorial weights of the complex monomials, without identifying an
abstract coefficient Hilbert space with the full holomorphic subspace.

Integration, density positivity, Hilbert-space completion and onto
isometry are separate obligations; this file records exact scalar
integral identities in the pinned Lean kernel.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Different monomial degrees have zero inner-product integral
for the normalized Gaussian area density (α/π)exp(-α‖z‖²). -/
theorem normalized_gaussian_mixed_monomial_eq_zero
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) (hmn : m ≠ n) :
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ m * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) = 0 := by
  rw [integral_const_mul,
    integral_gaussian_mixed_monomial_eq_zero alpha m n hmn,
    mul_zero]

/-- The exact diagonal norm factor under normalized Gaussian
area is n! α^{-n}. In particular the monomial basis must be scaled
by sqrt(α^n/n!) in the concrete Bargmann–Fock Hilbert space. -/
theorem integral_normalized_monomial_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ z : ℂ,
      (alpha / Real.pi) *
        (‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2))) =
      (Nat.factorial n : ℝ) * alpha ^ (-(n : ℝ)) := by
  rw [integral_const_mul, integral_monomial_norm_sq alpha ha n]
  have he : -((n : ℝ) + 1) = -(n : ℝ) + (-1) := by ring
  rw [he, Real.rpow_add ha, Real.rpow_neg_one]
  field_simp [ha.ne', Real.pi_ne_zero]

#print axioms GegenbauerFock.GaussianArea.normalized_gaussian_mixed_monomial_eq_zero
#print axioms GegenbauerFock.GaussianArea.integral_normalized_monomial_norm_sq

end GegenbauerFock.GaussianArea
