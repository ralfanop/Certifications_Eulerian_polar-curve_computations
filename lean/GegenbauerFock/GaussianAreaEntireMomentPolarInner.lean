import GegenbauerFock.GaussianAreaEntireMomentInner
import GegenbauerFock.GaussianAreaEntirePolarFubini

/-!
# V007 — intrinsic Gaussian L² coefficients as true planar and polar moments

Combines the independent genuine L² Hilbert coefficient computation with
the already certified weighted Lebesgue integral and actual polar Fubini.
No polynomial density, full Bargmann–Fock surjectivity, or unproved
interchange of integrals is assumed.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Every intrinsic entire Gaussian L² coefficient is the normalization
weight times the genuine planar Lebesgue Gaussian moment. -/
theorem normalizedMonomial_inner_eq_planar_entire_moment
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
    monomialWeight alpha n *
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha x z * star (z ^ n))) := by
  rw [normalizedMonomial_inner_entire_eq_moment alpha ha x n]
  congr 1
  rw [gaussianArea_integral_eq_volume alpha ha]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Each actual Hilbert coefficient is therefore the normalized
iterated radial/angular integral, with the Mathlib polar Jacobian.
The prior Fubini theorem supplies all required integrability. -/
theorem normalizedMonomial_inner_eq_iterated_polar_entire_moment
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
    monomialWeight alpha n *
      (∫ r in Set.Ioi (0 : ℝ),
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          r •
            (((alpha / Real.pi) *
                Real.exp (-alpha *
                  ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
              (entireRepresentative alpha x
                (Complex.polarCoord.symm (r, theta)) *
                star ((Complex.polarCoord.symm (r, theta)) ^ n)))) := by
  rw [normalizedMonomial_inner_eq_planar_entire_moment alpha ha x n]
  rw [entireRepresentative_planar_moment_eq_iterated_polar alpha ha x n]

#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_eq_planar_entire_moment
#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_eq_iterated_polar_entire_moment

end GegenbauerFock.GaussianArea
