import GegenbauerFock.GaussianAreaMonomialNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# V007 — angular Fourier orthogonality for Gaussian Fock monomials

The complex polar representation has an angular factor with integer
frequency m-n. The first step is exact cancellation of the nonzero
angular Fourier modes on a complete turn. This is a scalar angular
integral, not yet the full planar off-diagonal Gaussian integral.

The diagonal radial norm is separately certified. The integration
of the polar product and the onto Bargmann–Fock isometry remain open.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A nonzero integer Fourier mode has zero complex angular integral
over a complete positively oriented turn. -/
theorem integral_angular_mode_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ theta : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) = 0 := by
  have hkC : (k : ℂ) ≠ 0 := by
    exact_mod_cast hk
  have hc : (k : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero hkC Complex.I_ne_zero
  rw [intervalIntegral.integral_exp_mul_complex hc]
  have he :
      ((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- Angular cancellation for two distinct nonnegative monomial degrees. -/
theorem integral_angular_distinct_degrees_zero
    (m n : ℕ) (hmn : m ≠ n) :
    (∫ theta : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
          Complex.I) * (theta : ℂ))) = 0 := by
  apply integral_angular_mode_zero
  intro h
  apply hmn
  exact_mod_cast sub_eq_zero.mp h

#print axioms GegenbauerFock.GaussianArea.integral_angular_mode_zero
#print axioms GegenbauerFock.GaussianArea.integral_angular_distinct_degrees_zero

end GegenbauerFock.GaussianArea
