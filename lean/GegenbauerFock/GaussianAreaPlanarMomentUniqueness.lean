import GegenbauerFock.GaussianAreaCircleScalarExtraction
import GegenbauerFock.GaussianAreaRadialCircleMomentUniqueness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# V007 — intrinsic holomorphic Gaussian L² uniqueness from actual planar moments

This closes the exact analytic chain: true two-dimensional Gaussian
Lebesgue moment -> Fubini/polar chart -> normalized circle average ->
radial Taylor uniqueness. No assumed polynomial density or onto Fock
isometry occurs in any premise.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Genuine normalized Gaussian planar moment equals 2α times
the radial circular moment, with all Gaussian factors and
normalizations retained. -/
theorem entireRepresentative_planar_moment_eq_two_alpha_radial
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
    ((2 * alpha : ℝ) : ℂ) *
      (∫ r in Set.Ioi (0 : ℝ),
        ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
          Real.circleAverage
            (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n)) 0 r) := by
  rw [entireRepresentative_planar_moment_eq_radial_circleAverage alpha ha x n]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact gaussian_circleAverage_scalar_normalization alpha r
    (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))

/-- A vanishing genuine planar moment forces its corresponding
radial circular Gaussian moment to vanish, as α>0 makes 2α nonzero. -/
theorem radial_circleMoment_zero_of_planar_moment_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ)
    (hz :
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))) = 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
        Real.circleAverage
          (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n)) 0 r) = 0 := by
  rw [entireRepresentative_planar_moment_eq_two_alpha_radial alpha ha x n] at hz
  have hc : ((2 * alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha.ne'
  exact (mul_eq_zero.mp hz).resolve_left hc

/-- All genuine normalized planar Gaussian moments vanish only for
the zero intrinsic entire Gaussian L² vector. This is not an
abstract coefficient-space assertion or a conditional reduction. -/
theorem intrinsicGaussian_zero_of_all_planar_moments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (hz : ∀ n : ℕ,
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))) = 0) :
    x = 0 := by
  apply intrinsicGaussian_zero_of_radial_circleMoments_zero alpha ha x
  intro n
  exact radial_circleMoment_zero_of_planar_moment_zero
    alpha ha x n (hz n)

#print axioms GegenbauerFock.GaussianArea.entireRepresentative_planar_moment_eq_two_alpha_radial
#print axioms GegenbauerFock.GaussianArea.radial_circleMoment_zero_of_planar_moment_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicGaussian_zero_of_all_planar_moments_zero

end GegenbauerFock.GaussianArea
