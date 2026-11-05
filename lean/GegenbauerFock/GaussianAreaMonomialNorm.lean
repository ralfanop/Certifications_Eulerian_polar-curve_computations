import GegenbauerFock.GaussianAreaNormalization

/-!
# V007 — exact Gaussian diagonal monomial norms on the complex plane

These are the genuine two-dimensional Gaussian area integrals that give
the diagonal norm of each complex monomial in Bargmann–Fock space.
They are proved through pinned Mathlib's complex polar/Gamma integral,
not by replacing the plane integral with a one-dimensional proxy.

Orthogonality between distinct monomials and the onto Fock isometry
are separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The entire family of even radial moments of the complex Gaussian
area measure, with the exact factorial normalization. -/
theorem integral_even_radial_rpow
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * (n : ℝ)) *
      Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) =
      Real.pi * alpha ^ (-((n : ℝ) + 1)) *
        (Nat.factorial n : ℝ) := by
  have hq : (-2 : ℝ) < 2 * (n : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := 2 * (n : ℝ)) (b := alpha)
    (by norm_num) hq ha
  calc
    (∫ z : ℂ, ‖z‖ ^ (2 * (n : ℝ)) *
      Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) =
      (2 * Real.pi / 2) *
        alpha ^ (-(2 * (n : ℝ) + 2) / 2) *
        Real.Gamma ((2 * (n : ℝ) + 2) / 2) := by
        have hpow (z : ℂ) :
            ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ (2 : ℕ) := by
          simpa using (Real.rpow_natCast (‖z‖) (2 : ℕ))
        simpa only [hpow] using h
    _ = Real.pi * alpha ^ (-((n : ℝ) + 1)) *
        (Nat.factorial n : ℝ) := by
      have he : -(2 * (n : ℝ) + 2) / 2 =
          -((n : ℝ) + 1) := by ring
      have hg : (2 * (n : ℝ) + 2) / 2 =
          (n : ℝ) + 1 := by ring
      rw [he, hg, Real.Gamma_nat_eq_factorial]
      ring

/-- Squared L² Gaussian norm of the genuine complex monomial zⁿ.
The norm is calculated with planar Lebesgue measure. -/
theorem integral_monomial_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ z : ℂ, ‖z ^ n‖ ^ 2 *
      Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) =
      Real.pi * alpha ^ (-((n : ℝ) + 1)) *
        (Nat.factorial n : ℝ) := by
  have hterm (z : ℂ) :
      ‖z ^ n‖ ^ 2 = ‖z‖ ^ (2 * (n : ℝ)) := by
    calc
      ‖z ^ n‖ ^ 2 = (‖z‖ ^ n) ^ 2 := by rw [norm_pow]
      _ = ‖z‖ ^ (2 * n) := by rw [← pow_mul, mul_comm n 2]
      _ = ‖z‖ ^ (2 * (n : ℝ)) := by
        rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
  calc
    (∫ z : ℂ, ‖z ^ n‖ ^ 2 *
      Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) =
      (∫ z : ℂ, ‖z‖ ^ (2 * (n : ℝ)) *
        Real.exp (-alpha * ‖z‖ ^ 2) ∂volume) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hterm]
    _ = _ := integral_even_radial_rpow alpha ha n

#print axioms GegenbauerFock.GaussianArea.integral_even_radial_rpow
#print axioms GegenbauerFock.GaussianArea.integral_monomial_norm_sq

end GegenbauerFock.GaussianArea
