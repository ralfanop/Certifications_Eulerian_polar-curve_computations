import GegenbauerFock.GaussianAreaPolarAngularOrthogonality
import Mathlib.MeasureTheory.Integral.Prod

/-!
# V007 — Fourier cancellation on the actual complex polar product chart

Convert the certified interval integral on (-π,π) into the Lebesgue
set integral over the polar chart and factor the two-dimensional
radial-angular product using the genuine product measure.

This proves vanishing for every separable radial-angular profile at
nonzero integer frequency. Identifying the actual complex mixed
Gaussian monomials after polar substitution remains a separate step.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The Fourier cancellation over (-π,π) is also an exact set-integral
identity on the open angular support of Mathlib's polar chart. -/
theorem setIntegral_polar_angular_mode_zero
    (k : ℤ) (hk : k ≠ 0) :
    (∫ theta : ℝ in Set.Ioo (-Real.pi) Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) = 0 := by
  calc
    (∫ theta : ℝ in Set.Ioo (-Real.pi) Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) =
    (∫ theta : ℝ in Set.Ioc (-Real.pi) Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) :=
        (integral_Ioc_eq_integral_Ioo).symm
    _ = (∫ theta : ℝ in (-Real.pi)..Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) :=
        (intervalIntegral.integral_of_le
          (le_of_lt (by positivity : -Real.pi < Real.pi))).symm
    _ = 0 := integral_polar_angular_mode_zero k hk

/-- Any radial factor annihilates a nonzero angular Fourier mode
after integration against the full planar product measure restricted
to the actual polar-coordinate chart. -/
theorem polar_radial_angular_product_zero
    (k : ℤ) (hk : k ≠ 0) (radial : ℝ → ℂ) :
    (∫ p : ℝ × ℝ in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      radial p.1 *
        Complex.exp (((k : ℂ) * Complex.I) * (p.2 : ℂ))) = 0 := by
  rw [Measure.volume_eq_prod, setIntegral_prod_mul,
    setIntegral_polar_angular_mode_zero k hk, mul_zero]

/-- Product-integral orthogonality of angular profiles associated to
distinct monomial degrees, with arbitrary complex radial coefficient. -/
theorem polar_radial_distinct_degrees_product_zero
    (m n : ℕ) (hmn : m ≠ n) (radial : ℝ → ℂ) :
    (∫ p : ℝ × ℝ in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      radial p.1 *
        Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
          Complex.I) * (p.2 : ℂ))) = 0 := by
  apply polar_radial_angular_product_zero
  intro h
  apply hmn
  exact_mod_cast sub_eq_zero.mp h

#print axioms GegenbauerFock.GaussianArea.setIntegral_polar_angular_mode_zero
#print axioms GegenbauerFock.GaussianArea.polar_radial_angular_product_zero
#print axioms GegenbauerFock.GaussianArea.polar_radial_distinct_degrees_product_zero

end GegenbauerFock.GaussianArea
