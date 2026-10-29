import GegenbauerFock.GaussianAreaEntirePolarIntegrability
import GegenbauerFock.GaussianAreaPolarFubini

/-!
# V007 — Fubini for actual planar moments of arbitrary entire Gaussian L² vectors

This bridges the genuine normalized Gaussian planar integral of every
intrinsic entire L² representative to the iterated integral on the
complex polar chart. The full Jacobian-weighted pullback integrability
was certified separately; no Fubini interchange is postulated.

The exact circle-average normalization and Taylor uniqueness are
subsequent obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Fubini for every intrinsic entire Gaussian L² moment, with exact
Gaussian normalization, genuine two-dimensional volume and Jacobian. -/
theorem entireRepresentative_planar_moment_eq_iterated_polar
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
      (∫ r in Set.Ioi (0 : ℝ),
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          r •
            (((alpha / Real.pi) *
              Real.exp (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℝ) •
              (entireRepresentative alpha x
                (Complex.polarCoord.symm (r, theta)) *
                star ((Complex.polarCoord.symm (r, theta)) ^ n)))) := by
  exact planar_integral_eq_iterated_polar
    (fun z : ℂ =>
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n)))
    (entireRepresentative_polar_weighted_moment_integrable alpha ha x n)

#print axioms GegenbauerFock.GaussianArea.entireRepresentative_planar_moment_eq_iterated_polar

end GegenbauerFock.GaussianArea
