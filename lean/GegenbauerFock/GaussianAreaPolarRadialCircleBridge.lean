import GegenbauerFock.GaussianAreaPolarCircleAverage
import GegenbauerFock.GaussianAreaEntirePolarFubini
import GegenbauerFock.GaussianAreaPolarMixedPullback

/-!
# V007 — genuine planar Gaussian moments as radial circle averages

For the complex polar chart (-π,π), the normalized circle average
is linked to the true angular integral by an independently certified
identity. We transport this through the outer radial integral and
apply it to the actual weighted Gaussian moments of intrinsic entire
L² representatives, retaining the Jacobian and exact normalization.

No polynomial-density, moment–Taylor, or onto theorem is assumed.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Integrate the exact angular circle-average identity in the radial
variable, allowing the complex-plane integrand itself to depend on r. -/
theorem iterated_polar_eq_radial_circleAverage
    (f : ℝ → ℂ → ℂ) :
    (∫ r in Set.Ioi (0 : ℝ),
      ∫ theta in Set.Ioo (-Real.pi) Real.pi,
        f r (Complex.polarCoord.symm (r, theta))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (2 * Real.pi) • Real.circleAverage (f r) 0 r) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact polar_angular_integral_eq_two_pi_circleAverage (f r) r

/-- True normalized complex-plane Lebesgue Gaussian moments equal
the iterated radial integral of a normalized circle average, with
the polar Jacobian and Gaussian density preserved exactly. -/
theorem entireRepresentative_planar_moment_eq_radial_circleAverage
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (2 * Real.pi) •
        Real.circleAverage
          (fun z : ℂ =>
            r • (((alpha / Real.pi) *
              Real.exp (-alpha * r ^ 2) : ℝ) •
                (entireRepresentative alpha x z * star (z ^ n))))
          0 r) := by
  rw [entireRepresentative_planar_moment_eq_iterated_polar alpha ha x n]
  rw [← iterated_polar_eq_radial_circleAverage
    (fun (r : ℝ) (z : ℂ) =>
      r • (((alpha / Real.pi) *
        Real.exp (-alpha * r ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  apply setIntegral_congr_fun measurableSet_Ioo
  intro theta htheta
  rw [polar_gaussian_weight_eq alpha (r, theta) ⟨hr, htheta⟩]

#print axioms GegenbauerFock.GaussianArea.iterated_polar_eq_radial_circleAverage
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_planar_moment_eq_radial_circleAverage

end GegenbauerFock.GaussianArea
