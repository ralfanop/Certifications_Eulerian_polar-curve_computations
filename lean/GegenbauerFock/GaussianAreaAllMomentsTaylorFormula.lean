import GegenbauerFock.GaussianAreaPlanarMomentUniqueness
import GegenbauerFock.GaussianAreaRadialCircleTaylor

/-!
# V007 — exact Gaussian planar moment formula for every Taylor derivative

This strengthens moment uniqueness into an individual identity for
each Taylor derivative of every intrinsic entire Gaussian L² function.
The complex-plane integral is the actual two-dimensional Lebesgue
Gaussian moment, with the normalization alpha/pi and full Jacobian.
No density hypothesis is inserted.

The radial Gamma constant and the factorial denominator are retained
explicitly to keep the identity independent of any implicit
real-power simplification.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Every genuine normalized planar Gaussian conjugate-monomial moment
extracts the n-th complex Taylor derivative at the origin, with the
exact radial Gamma normalization. -/
theorem intrinsicEntire_planar_gaussian_moment_eq_taylor
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
      ((2 * alpha : ℝ) : ℂ) *
        (((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
          (Nat.factorial n : ℝ) : ℝ) : ℂ) *
          (iteratedDeriv n (entireRepresentative alpha x) 0 /
            (Nat.factorial n : ℂ))) := by
  rw [entireRepresentative_planar_moment_eq_two_alpha_radial alpha ha x n]
  rw [integral_radial_circleAverage_eq_taylorCoeff alpha ha
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) n]

/-- A single genuine planar Gaussian moment vanishes if and only if
the corresponding complex Taylor derivative at zero vanishes.
This equivalence is pointwise in n, without postulating density. -/
theorem intrinsicEntire_planar_moment_zero_iff_taylor_deriv_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) = 0 ↔
      iteratedDeriv n (entireRepresentative alpha x) 0 = 0 := by
  rw [intrinsicEntire_planar_gaussian_moment_eq_taylor alpha ha x n]
  have htwo : ((2 * alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ha))
  have hgamma :
      (((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 <
        alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
          (Nat.factorial n : ℝ) :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos ha _) (by norm_num))
        (by positivity)
    exact_mod_cast (ne_of_gt hpos)
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast (show (Nat.factorial n : ℝ) ≠ 0 by positivity)
  constructor
  · intro hz
    have hdiv :
        iteratedDeriv n (entireRepresentative alpha x) 0 /
          (Nat.factorial n : ℂ) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htwo)).resolve_left hgamma
    have h := congrArg (fun v : ℂ => v * (Nat.factorial n : ℂ)) hdiv
    simpa [div_eq_mul_inv, mul_assoc, hfac] using h
  · intro hz
    simp [hz]

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_planar_gaussian_moment_eq_taylor
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_planar_moment_zero_iff_taylor_deriv_zero

end GegenbauerFock.GaussianArea
