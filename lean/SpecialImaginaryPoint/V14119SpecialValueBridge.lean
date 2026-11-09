import Mathlib
import SpecialImaginaryPoint.V14119PrioritiesCertificate
import SpecialImaginaryPoint.Corollary36Analytic

/-!
# Manuscript 14.119 — true analytic special-value bridge (Proposition 2.1)

This reuses the existing actual Eulerian entire function and proves the
hyperbolic specialization on the imaginary axis and its convergent rational series.

The named Bessel and hypergeometric identifications, and the all-N tail
enclosure of Corollary 2.2, are deliberately not claimed by this module.
-/

namespace SpecialImaginaryPoint.V14119SpecialValue

/-- The actual entire Eulerian function on the imaginary axis is
the real hyperbolic-sine quotient. -/
theorem eulerian_profile_pure_imaginary (x : ℝ) (hx : x ≠ 0) :
    EulerianSpecialPoint.eulerianEvenAnalytic (2 * (x : ℂ) * Complex.I) =
      ((Real.sinh x / x : ℝ) : ℂ) := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hz : 2 * (x : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hxc) hI
  rw [EulerianSpecialPoint.eulerianEvenAnalytic_eq_sinc]
  simp only [EulerianSpecialPoint.eulerianSinc, if_neg hz]
  have harg : (2 * (x : ℂ) * Complex.I) / 2 = (x : ℂ) * Complex.I := by ring
  rw [harg, Complex.sin_mul_I, ← Complex.ofReal_sinh, Complex.ofReal_div]
  field_simp [hxc, hI] <;> ring

private theorem sqrt8_nonzero : Real.sqrt (8 : ℝ) ≠ 0 := by positivity

/-- The positive imaginary point corresponding to a=1/sqrt(8). -/
noncomputable def specialPoint : ℂ :=
  2 * ((1 / Real.sqrt (8 : ℝ) : ℝ) : ℂ) * Complex.I

/-- The profile genuinely equals the exact rational sum of Proposition 2.1. -/
theorem eulerian_profile_special_series :
    EulerianSpecialPoint.eulerianEvenAnalytic specialPoint =
      ((∑' n : ℕ,
        (1 : ℝ) / ((8 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ))) : ℂ) := by
  let a : ℝ := 1 / Real.sqrt 8
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hs : Real.sinh a / a = Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) := by
    dsimp [a]
    field_simp [sqrt8_nonzero] <;> ring
  change EulerianSpecialPoint.eulerianEvenAnalytic (2 * (a : ℂ) * Complex.I) = _
  rw [eulerian_profile_pure_imaginary a ha, hs]
  exact_mod_cast V14119Priorities.real_special_value_eq_series

/-- Certified strict rational interval, now for the actual Eulerian profile. -/
theorem eulerian_profile_special_bracket :
    (1020963929 : ℝ) / 10 ^ 9 <
      (EulerianSpecialPoint.eulerianEvenAnalytic specialPoint).re ∧
    (EulerianSpecialPoint.eulerianEvenAnalytic specialPoint).re <
      (1020963930 : ℝ) / 10 ^ 9 := by
  have ha : (1 / Real.sqrt (8 : ℝ) : ℝ) ≠ 0 := by positivity
  have hs : Real.sinh (1 / Real.sqrt 8) / (1 / Real.sqrt 8) =
      Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) := by
    field_simp [sqrt8_nonzero] <;> ring
  have heq := eulerian_profile_pure_imaginary (1 / Real.sqrt 8) ha
  change EulerianSpecialPoint.eulerianEvenAnalytic specialPoint = _ at heq
  rw [hs] at heq
  have hre : (EulerianSpecialPoint.eulerianEvenAnalytic specialPoint).re =
      Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) := by
    rw [heq]
    exact Complex.ofReal_re _
  rw [hre]
  exact V14119Priorities.real_special_value_rational_bracket

#print axioms SpecialImaginaryPoint.V14119SpecialValue.eulerian_profile_pure_imaginary
#print axioms SpecialImaginaryPoint.V14119SpecialValue.eulerian_profile_special_series
#print axioms SpecialImaginaryPoint.V14119SpecialValue.eulerian_profile_special_bracket

end SpecialImaginaryPoint.V14119SpecialValue
