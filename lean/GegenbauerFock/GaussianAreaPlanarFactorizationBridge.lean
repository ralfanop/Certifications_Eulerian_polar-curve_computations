import GegenbauerFock.GaussianAreaPolarProductOrthogonality

/-!
# V007 — lifting separable polar cancellation to genuine complex area

The pinned Mathlib theorem `Complex.integral_comp_polarCoord_symm`
identifies a genuine planar Lebesgue integral with its radial-angular
Jacobian pullback. The first theorem below combines that change of
variables with the already certified product cancellation.

The second theorem specializes the bridge to an actual Gaussian
mixed-monomial integrand, under an explicit pointwise polar
factorization hypothesis. Proving that hypothesis for all m ≠ n
is a separate task, not an assumption-free conclusion here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A genuinely two-dimensional integral vanishes when its polar
Jacobian pullback separates into a radial factor and a nonzero
integer angular Fourier mode. -/
theorem planar_integral_zero_of_polar_factorization
    (k : ℤ) (hk : k ≠ 0) (radial : ℝ → ℂ) (f : ℂ → ℂ)
    (hfactor :
      ∀ p : ℝ × ℝ,
        p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi →
        p.1 • f (Complex.polarCoord.symm p) =
          radial p.1 *
            Complex.exp (((k : ℂ) * Complex.I) * (p.2 : ℂ))) :
    (∫ z : ℂ, f z) = 0 := by
  calc
    (∫ z : ℂ, f z) =
        (∫ p : ℝ × ℝ in Complex.polarCoord.target,
          p.1 • f (Complex.polarCoord.symm p)) :=
      (Complex.integral_comp_polarCoord_symm f).symm
    _ = (∫ p : ℝ × ℝ in
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        radial p.1 *
          Complex.exp (((k : ℂ) * Complex.I) * (p.2 : ℂ))) := by
      rw [Complex.polarCoord_target]
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact hfactor p hp
    _ = 0 := polar_radial_angular_product_zero k hk radial

/-- Reduction of genuine off-diagonal Gaussian complex monomial
orthogonality to the explicit pointwise polar factorization of the
mixed monomial. That algebraic factorization remains to be certified. -/
theorem gaussian_mixed_monomial_zero_of_polar_factorization
    (alpha : ℝ) (m n : ℕ) (hmn : m ≠ n)
    (radial : ℝ → ℂ)
    (hfactor :
      ∀ p : ℝ × ℝ,
        p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi →
        p.1 •
            ((Complex.polarCoord.symm p) ^ m *
              star ((Complex.polarCoord.symm p) ^ n) *
              (Real.exp
                (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) : ℂ)) =
          radial p.1 *
            Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
              Complex.I) * (p.2 : ℂ))) :
    (∫ z : ℂ,
        z ^ m * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) = 0 := by
  have hk : (m : ℤ) - (n : ℤ) ≠ 0 := by
    intro h
    apply hmn
    exact_mod_cast sub_eq_zero.mp h
  exact planar_integral_zero_of_polar_factorization
    ((m : ℤ) - (n : ℤ)) hk radial
    (fun z : ℂ =>
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) hfactor

#print axioms GegenbauerFock.GaussianArea.planar_integral_zero_of_polar_factorization
#print axioms GegenbauerFock.GaussianArea.gaussian_mixed_monomial_zero_of_polar_factorization

end GegenbauerFock.GaussianArea
