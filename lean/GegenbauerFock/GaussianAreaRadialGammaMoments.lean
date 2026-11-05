import GegenbauerFock.GaussianAreaAngularMomentUniqueness
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# V007 — exact positive radial Gamma moments for Gaussian angular extraction

The radial factor accompanying the nth conjugate-monomial angular
moment has the exact factorial/Gamma value on the positive real ray.
In particular this coefficient is strictly positive and cannot
annihilate a Taylor coefficient.

The remaining analytic step is the Fubini/polar change-of-variables
identity for an arbitrary intrinsic entire Gaussian L² representative,
relating its genuine *planar* monomial moment to this radial factor
times the circular Fourier/Taylor coefficient. That identity and
onto Fock surjectivity are not claimed here.
-/

noncomputable section

open Real MeasureTheory Set

namespace GegenbauerFock.GaussianArea

/-- Exact positive-ray radial integral required for the nth
Gaussian holomorphic moment-to-Taylor calculation. -/
theorem integral_radial_gaussian_even_power
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (∫ r in Set.Ioi (0 : ℝ),
      r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2)) =
      alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
        (Nat.factorial n : ℝ) := by
  have hq : (-1 : ℝ) < (((2 * n + 1 : ℕ) : ℝ)) := by
    have hnonneg : (0 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
    linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (((2 * n + 1 : ℕ) : ℝ)))
    (b := alpha) (by norm_num) hq ha
  have hgamma :
      ((((2 * n + 1 : ℕ) : ℝ) + 1) / 2) = (n : ℝ) + 1 := by
    push_cast
    ring
  have hexponent :
      -((((2 * n + 1 : ℕ) : ℝ) + 1)) / (2 : ℝ) =
        -((n : ℝ) + 1) := by
    push_cast
    ring
  rw [hgamma, hexponent, Real.Gamma_nat_eq_factorial] at h
  have htwo (r : ℝ) : r ^ (2 : ℝ) = r ^ (2 : ℕ) := by
    simpa using (Real.rpow_natCast r (2 : ℕ))
  simpa only [Real.rpow_natCast, htwo] using h

/-- The radial Gaussian coefficient multiplying the nth Taylor
coefficient in the polar Fock moment formula is nonzero. -/
theorem integral_radial_gaussian_even_power_pos
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    0 <
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (2 * n + 1) * Real.exp (-alpha * r ^ 2)) := by
  rw [integral_radial_gaussian_even_power alpha ha n]
  have hfactorial : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos ha _) (by norm_num))
    hfactorial

#print axioms GegenbauerFock.GaussianArea.integral_radial_gaussian_even_power
#print axioms GegenbauerFock.GaussianArea.integral_radial_gaussian_even_power_pos

end GegenbauerFock.GaussianArea
