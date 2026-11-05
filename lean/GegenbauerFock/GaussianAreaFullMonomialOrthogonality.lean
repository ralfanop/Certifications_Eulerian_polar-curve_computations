import GegenbauerFock.GaussianAreaPolarAngularAlgebra
import GegenbauerFock.GaussianAreaPolarMixedPullback

/-!
# V007 — unconditional planar Gaussian orthogonality of distinct monomials

Formal algebraic factorization of mixed complex monomials in Mathlib's
true polar chart, including the radial Jacobian and the Gaussian
weight. Combining the pointwise identity with the previously verified
polar-product cancellation and complex polar change of variables
produces the off-diagonal Gaussian orthogonality identity.

This is a new CI candidate: the statements are not considered
certified until the pinned Lean compilation and axiom audit succeed.
The onto Gaussian holomorphic Bargmann–Fock isometry remains open.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The conjugated complex monomial has radial factor r^(m+n)
and angular Fourier frequency m-n. -/
theorem polar_mixed_monomial_eq_radial_exp
    (p : ℝ × ℝ) (m n : ℕ) :
    (Complex.polarCoord.symm p) ^ m *
      star ((Complex.polarCoord.symm p) ^ n) =
    (p.1 : ℂ) ^ (m + n) *
      Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
        Complex.I) * (p.2 : ℂ)) := by
  rw [polarCoord_symm_eq_radius_exp]
  simp only [mul_pow, star_mul, star_pow]
  have hr : star (p.1 : ℂ) = (p.1 : ℂ) := by
    simp [Complex.star_def]
  rw [hr]
  have hf := exp_monomial_angular_frequency p.2 m n
  simp only [star_pow] at hf
  rw [← hf, pow_add]
  ring

/-- Pointwise polar factorization of the actual Gaussian mixed
complex monomial, including its radial Jacobian p.1. -/
theorem polar_gaussian_mixed_monomial_factorization
    (alpha : ℝ) (m n : ℕ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :
    p.1 •
      ((Complex.polarCoord.symm p) ^ m *
        star ((Complex.polarCoord.symm p) ^ n) *
        (Real.exp (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) : ℂ)) =
    ((p.1 : ℂ) ^ (m + n + 1) *
      (Real.exp (-alpha * p.1 ^ 2) : ℂ)) *
      Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
        Complex.I) * (p.2 : ℂ)) := by
  rw [Complex.real_smul, polar_gaussian_weight_eq alpha p hp,
    polar_mixed_monomial_eq_radial_exp p m n, pow_succ]
  ring

/-- Exact off-diagonal orthogonality of complex monomials under the
planar Gaussian Lebesgue weight, with no extra factorization axiom. -/
theorem integral_gaussian_mixed_monomial_eq_zero
    (alpha : ℝ) (m n : ℕ) (hmn : m ≠ n) :
    (∫ z : ℂ,
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) = 0 := by
  apply gaussian_mixed_monomial_zero_of_polar_factorization
    alpha m n hmn
    (fun r : ℝ =>
      (r : ℂ) ^ (m + n + 1) *
        (Real.exp (-alpha * r ^ 2) : ℂ))
  intro p hp
  exact polar_gaussian_mixed_monomial_factorization alpha m n p hp

#print axioms GegenbauerFock.GaussianArea.polar_mixed_monomial_eq_radial_exp
#print axioms GegenbauerFock.GaussianArea.polar_gaussian_mixed_monomial_factorization
#print axioms GegenbauerFock.GaussianArea.integral_gaussian_mixed_monomial_eq_zero

end GegenbauerFock.GaussianArea
