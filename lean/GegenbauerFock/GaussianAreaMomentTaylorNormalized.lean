import GegenbauerFock.GaussianAreaAllMomentsTaylorFormula

/-!
# V007 — simplified exact planar Gaussian moment–Taylor formula

The previously kernel-certified general Gaussian moment identity
has a Gamma/factorial scalar. This module removes that factor without
changing the integral or the intrinsic entire Gaussian L² space.

The final equality is the standard closed-form Gaussian moment law,
including its exact power of alpha.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The real Gaussian Gamma multiplier reduces to alpha⁻ⁿ.
This is a scalar identity and does not assume any analytic theorem. -/
theorem gaussian_taylor_gamma_scalar_normalization
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (2 * alpha) *
        (alpha ^ (-((n : ℝ) + 1)) * (1 / 2)) =
      alpha ^ (-(n : ℝ)) := by
  have hnplus :
      alpha ^ (-((n : ℝ) + 1)) =
        (alpha ^ (n + 1))⁻¹ := by
    rw [show -((n : ℝ) + 1) = -(((n + 1 : ℕ) : ℝ)) by
      push_cast
      ring]
    rw [Real.rpow_neg (le_of_lt ha), Real.rpow_natCast]
  have hnminus :
      alpha ^ (-(n : ℝ)) = (alpha ^ n)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt ha), Real.rpow_natCast]
  calc
    (2 * alpha) *
        (alpha ^ (-((n : ℝ) + 1)) * (1 / 2)) =
      (2 * alpha) * ((alpha ^ (n + 1))⁻¹ * (1 / 2)) := by
        rw [hnplus]
    _ = (alpha ^ n)⁻¹ := by
      rw [pow_succ]
      field_simp [ha.ne', pow_ne_zero n ha.ne']
      <;> ring
    _ = alpha ^ (-(n : ℝ)) := hnminus.symm

/-- For an intrinsic entire Gaussian L² function, the genuine
two-dimensional planar normalized moment is exactly its n-th Taylor
derivative at zero multiplied by alpha⁻ⁿ. -/
theorem intrinsicEntire_planar_gaussian_moment_eq_scaled_derivative
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) =
      ((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
        iteratedDeriv n (entireRepresentative alpha x) 0 := by
  rw [intrinsicEntire_planar_gaussian_moment_eq_taylor alpha ha x n]
  have hscalar :
      (2 * alpha) *
          (alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
            (Nat.factorial n : ℝ)) =
        alpha ^ (-(n : ℝ)) * (Nat.factorial n : ℝ) := by
    have h := gaussian_taylor_gamma_scalar_normalization alpha ha n
    calc
      _ = ((2 * alpha) *
          (alpha ^ (-((n : ℝ) + 1)) * (1 / 2))) *
            (Nat.factorial n : ℝ) := by ring
      _ = _ := by rw [h]
  have hc :
      ((2 * alpha : ℝ) : ℂ) *
        (((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
          (Nat.factorial n : ℝ) : ℝ) : ℂ) =
        (((alpha ^ (-(n : ℝ)) *
          (Nat.factorial n : ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast hscalar
  rw [← mul_assoc, hc]
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast (show (Nat.factorial n : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp [hfac]
  <;> ring

#print axioms GegenbauerFock.GaussianArea.gaussian_taylor_gamma_scalar_normalization
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_planar_gaussian_moment_eq_scaled_derivative

end GegenbauerFock.GaussianArea
