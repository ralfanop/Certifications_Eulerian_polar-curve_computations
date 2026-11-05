import GegenbauerFock.GaussianAreaEntireMomentPolarInner
import GegenbauerFock.GaussianAreaPolarAngularMoment

/-! V007 — true Gaussian L² monomial coefficients as actual radial circle moments.
No polynomial density or onto theorem is assumed. -/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GaussianArea

theorem gaussian_angular_scalar_eq (alpha r : ℝ) :
    (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) * (2 * Real.pi) =
      (2 * alpha) * (r * Real.exp (-alpha * r ^ 2)) := by
  field_simp [Real.pi_ne_zero]

theorem polar_gaussian_angular_eq_radial
    (alpha r : ℝ) (hr : 0 < r) (g : ℂ → ℂ) :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi,
      r • (((alpha / Real.pi) *
        Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
          g (Complex.polarCoord.symm (r, theta)))) =
    (2 * alpha) • ((r * Real.exp (-alpha * r ^ 2)) •
      Real.circleAverage g 0 r) := by
  calc
    _ = (r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) •
          ((2 * Real.pi) • Real.circleAverage g 0 r) :=
        polar_gaussian_angular_integral_eq_circleAverage alpha r hr g
    _ = ((r * ((alpha / Real.pi) * Real.exp (-alpha * r ^ 2))) *
          (2 * Real.pi)) • Real.circleAverage g 0 r := by rw [smul_smul]
    _ = ((2 * alpha) * (r * Real.exp (-alpha * r ^ 2))) •
          Real.circleAverage g 0 r := by rw [gaussian_angular_scalar_eq]
    _ = (2 * alpha) • ((r * Real.exp (-alpha * r ^ 2)) •
          Real.circleAverage g 0 r) := by rw [smul_smul]

theorem normalizedMonomial_inner_eq_radial_circleAverage
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
    monomialWeight alpha n * ((2 * alpha) •
      (∫ r in Set.Ioi (0 : ℝ),
        (r * Real.exp (-alpha * r ^ 2)) •
          Real.circleAverage (fun z : ℂ =>
            entireRepresentative alpha x z * star (z ^ n)) 0 r)) := by
  rw [normalizedMonomial_inner_eq_iterated_polar_entire_moment alpha ha x n]
  congr 1
  calc
    _ = (∫ r in Set.Ioi (0 : ℝ),
      (2 * alpha) • ((r * Real.exp (-alpha * r ^ 2)) •
        Real.circleAverage (fun z : ℂ =>
          entireRepresentative alpha x z * star (z ^ n)) 0 r)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          exact polar_gaussian_angular_eq_radial alpha r hr
            (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
    _ = (2 * alpha) •
      (∫ r in Set.Ioi (0 : ℝ),
        (r * Real.exp (-alpha * r ^ 2)) •
          Real.circleAverage (fun z : ℂ =>
            entireRepresentative alpha x z * star (z ^ n)) 0 r) := by
          rw [integral_smul]

#print axioms GegenbauerFock.GaussianArea.gaussian_angular_scalar_eq
#print axioms GegenbauerFock.GaussianArea.polar_gaussian_angular_eq_radial
#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_eq_radial_circleAverage

end GegenbauerFock.GaussianArea
