import GegenbauerFock.GaussianAreaPolarProductOrthogonality

/-!
# V007 — genuine planar Gaussian mixed monomials in complex polar coordinates

These identities retain the actual complex Lebesgue integral and the
Jacobian in Mathlib's complex polar chart. They prepare the remaining
identification of the mixed monomial with a separable angular Fourier mode.

No off-diagonal Gaussian orthogonality or onto Fock isometry is asserted.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The exact radial Gaussian weight on the open polar chart, without
changing the planar Gaussian integrand or its normalization. -/
theorem polar_gaussian_weight_eq
    (alpha : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :
    Real.exp (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) =
      Real.exp (-alpha * p.1 ^ 2) := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]

/-- Change of variables for the actual off-diagonal Gaussian monomial
integral on the complex plane, with the true radial Jacobian p.1. -/
theorem integral_gaussian_mixed_monomial_eq_polar
    (alpha : ℝ) (m n : ℕ) :
    (∫ z : ℂ,
      (z ^ m) * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) =
    (∫ p : ℝ × ℝ in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 •
        ((Complex.polarCoord.symm p) ^ m *
          star ((Complex.polarCoord.symm p) ^ n) *
          (Real.exp
            (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) : ℂ))) := by
  exact
    (Complex.integral_comp_polarCoord_symm
      (f := fun z : ℂ =>
        (z ^ m) * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))).symm

#print axioms GegenbauerFock.GaussianArea.polar_gaussian_weight_eq
#print axioms GegenbauerFock.GaussianArea.integral_gaussian_mixed_monomial_eq_polar

end GegenbauerFock.GaussianArea
