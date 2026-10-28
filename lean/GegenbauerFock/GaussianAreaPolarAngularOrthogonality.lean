import GegenbauerFock.GaussianAreaAngularOrthogonality
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# V007 — angular cancellation in the actual complex polar coordinate chart

Mathlib's complex polar change of variables uses the angular interval
(-π,π), not (0,2π). This module establishes the exact Fourier cancellation
for that specific chart and all distinct natural monomial degrees.

The full two-dimensional mixed Gaussian integral still requires the
polar product-integrability and Fubini steps; it is not claimed here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Cancellation of a nonzero Fourier frequency on precisely the
angular interval of Mathlib's complex polar chart (-π,π). -/
theorem integral_polar_angular_mode_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ theta : ℝ in (-Real.pi)..Real.pi,
        Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) = 0 := by
  have hkC : (k : ℂ) ≠ 0 := by
    exact_mod_cast hk
  have hc : (k : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero hkC Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have he :
      ((k : ℂ) * Complex.I) * ((Real.pi : ℝ) : ℂ) =
      ((k : ℂ) * Complex.I) * ((-Real.pi : ℝ) : ℂ) +
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The angular factors of distinct Gaussian holomorphic monomials
integrate to zero on the exact (-π,π) polar chart. -/
theorem integral_polar_distinct_degrees_zero
    (m n : ℕ) (hmn : m ≠ n) :
    (∫ theta : ℝ in (-Real.pi)..Real.pi,
        Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
          Complex.I) * (theta : ℂ))) = 0 := by
  apply integral_polar_angular_mode_zero
  intro h
  apply hmn
  exact_mod_cast sub_eq_zero.mp h

#print axioms GegenbauerFock.GaussianArea.integral_polar_angular_mode_zero
#print axioms GegenbauerFock.GaussianArea.integral_polar_distinct_degrees_zero

end GegenbauerFock.GaussianArea
