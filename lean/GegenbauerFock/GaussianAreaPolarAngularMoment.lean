import GegenbauerFock.GaussianAreaPolarRadialDensity
import GegenbauerFock.GaussianAreaPolarCircleAverage

/-!
# V007 — exact angular Gaussian moment on the genuine complex polar chart

On positive radii, the Gaussian factor and polar Jacobian are radial,
so the angular Bochner integral is precisely the scalar radial weight
times 2π times the normalized circle average. This does not assume
polynomial density or Fock surjectivity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Exact angular-to-circle-average identity with the positive radial
Jacobian and the normalized planar Gaussian density. -/
theorem polar_gaussian_angular_integral_eq_circleAverage
    (alpha r : ℝ) (hr : 0 < r) (g : ℂ → ℂ) :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi,
      r •
        (((alpha / Real.pi) *
          Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
          g (Complex.polarCoord.symm (r, theta)))) =
      (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
        ((2 * Real.pi) • Real.circleAverage g 0 r) := by
  calc
    (∫ theta in Set.Ioo (-Real.pi) Real.pi,
      r •
        (((alpha / Real.pi) *
          Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
          g (Complex.polarCoord.symm (r, theta)))) =
      (∫ theta in Set.Ioo (-Real.pi) Real.pi,
        (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
          g (Complex.polarCoord.symm (r, theta))) := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro theta _
            exact gaussian_polar_weighted_smul_eq_radial alpha r theta hr g
    _ = (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
        (∫ theta in Set.Ioo (-Real.pi) Real.pi,
          g (Complex.polarCoord.symm (r, theta))) := by
            rw [integral_smul]
    _ = (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
        ((2 * Real.pi) • Real.circleAverage g 0 r) := by
            rw [polar_angular_integral_eq_two_pi_circleAverage]

#print axioms GegenbauerFock.GaussianArea.polar_gaussian_angular_integral_eq_circleAverage

end GegenbauerFock.GaussianArea
