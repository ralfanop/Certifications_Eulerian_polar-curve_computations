import GegenbauerFock.GaussianAreaPolarAngularAlgebra

/-!
# V007 — radiality of the true normalized Gaussian density in complex polar coordinates

The Gaussian weight is constant along each positive-radius circle of the
actual complex polar-coordinate chart. This is an analytic/algebraic
prerequisite for moving the Gaussian density outside the angular integral;
no Fock density or surjectivity is used.
-/

noncomputable section

namespace GegenbauerFock.GaussianArea

/-- The norm of the actual polar point is its positive radial coordinate. -/
theorem norm_polarCoord_symm_of_pos
    (r theta : ℝ) (hr : 0 < r) :
    ‖Complex.polarCoord.symm (r, theta)‖ = r := by
  rw [polarCoord_symm_eq_radius_exp]
  simp [norm_mul, Complex.norm_exp, Complex.mul_re, abs_of_pos hr]

/-- The normalized Gaussian density has no angular dependence
on the positive-radius part of the polar chart. -/
theorem gaussian_polar_density_eq_radial
    (alpha r theta : ℝ) (hr : 0 < r) :
    (alpha / Real.pi) *
      Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) =
    (alpha / Real.pi) * Real.exp (-alpha * r ^ 2) := by
  rw [norm_polarCoord_symm_of_pos r theta hr]

/-- Including the exact polar Jacobian r, the Gaussian weighted
integrand is a radial scalar multiple of the angular function. -/
theorem gaussian_polar_weighted_smul_eq_radial
    (alpha r theta : ℝ) (hr : 0 < r) (g : ℂ → ℂ) :
    r •
      (((alpha / Real.pi) *
        Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
          g (Complex.polarCoord.symm (r, theta))) =
    (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
      g (Complex.polarCoord.symm (r, theta)) := by
  rw [gaussian_polar_density_eq_radial alpha r theta hr, smul_smul]

#print axioms GegenbauerFock.GaussianArea.norm_polarCoord_symm_of_pos
#print axioms GegenbauerFock.GaussianArea.gaussian_polar_density_eq_radial
#print axioms GegenbauerFock.GaussianArea.gaussian_polar_weighted_smul_eq_radial

end GegenbauerFock.GaussianArea
