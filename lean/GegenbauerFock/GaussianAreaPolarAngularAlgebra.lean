import GegenbauerFock.GaussianAreaPlanarFactorizationBridge
import Mathlib.Analysis.Complex.Trigonometric

/-!
# V007 — algebraic angular factor of complex Gaussian monomials

This file isolates the two elementary complex identities needed to
discharge the pointwise polar factorization in
`GaussianAreaPlanarFactorizationBridge`:
the exponential form of the polar coordinate map, and the conjugate
monomial angular frequency m-n.

These are algebraic identities; no unconditional planar orthogonality
or Bargmann–Fock isometry is claimed in this module.
-/

noncomputable section

namespace GegenbauerFock.GaussianArea

/-- Complex polar coordinates are exactly radius times an angular
complex exponential, with no normalization or dimensional shortcut. -/
theorem polarCoord_symm_eq_radius_exp (p : ℝ × ℝ) :
    Complex.polarCoord.symm p =
      (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]

/-- Conjugation reverses the imaginary angular exponent. -/
theorem star_exp_angle (theta : ℝ) :
    star (Complex.exp ((theta : ℂ) * Complex.I)) =
      Complex.exp (-((theta : ℂ) * Complex.I)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- The mixed exponential monomial has the Fourier frequency m-n. -/
theorem exp_monomial_angular_frequency
    (theta : ℝ) (m n : ℕ) :
    Complex.exp ((theta : ℂ) * Complex.I) ^ m *
      star (Complex.exp ((theta : ℂ) * Complex.I) ^ n) =
    Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
      Complex.I) * (theta : ℂ)) := by
  rw [star_pow, star_exp_angle]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

#print axioms GegenbauerFock.GaussianArea.polarCoord_symm_eq_radius_exp
#print axioms GegenbauerFock.GaussianArea.star_exp_angle
#print axioms GegenbauerFock.GaussianArea.exp_monomial_angular_frequency

end GegenbauerFock.GaussianArea
