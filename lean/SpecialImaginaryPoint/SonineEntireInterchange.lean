import Mathlib
import SpecialImaginaryPoint.SonineEvenComplexPolynomials

/-!
# Manuscript 14.1 §4 — rigorous series/integral interchange at a complex parameter

For a complex coefficient sequence `a` and parameter `z`, assume
`Summable (fun n => ‖a n * z^(2*n)‖)`. We establish the *actual* dominated
convergence interchange between the infinite even Taylor series evaluated
at `z * sqrt(1-u²)` and the Sonine interval integral over `u ∈ [-1,1]`.

This is a local summability / analytic integration theorem. Proving
regularity and the global radial differential equation at ALL complex
points requires a further step.
-/

namespace Manuscript14Sonine

open MeasureTheory intervalIntegral

private theorem sonine_sqrt_norm_le_one (u : ℝ)
    (hu : u ∈ Set.uIcc (-1 : ℝ) 1) :
    ‖(Real.sqrt (1 - u^2) : ℂ)‖ ≤ 1 := by
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  rcases hu with ⟨hlo,hhi⟩
  have hpos : 0 ≤ 1 - u^2 := by nlinarith [mul_nonneg (show 0 ≤ 1-u by linarith) (show 0 ≤ 1+u by linarith)]
  have hsq := Real.sq_sqrt hpos
  have hsge := Real.sqrt_nonneg (1-u^2)
  have hsle : Real.sqrt (1-u^2) ≤ 1 := by nlinarith [sq_nonneg u]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsge] using hsle

private theorem sonine_integrand_norm_le (a : ℕ → ℂ) (z : ℂ)
    (n : ℕ) (u : ℝ) (hu : u ∈ Set.uIcc (-1 : ℝ) 1) :
    ‖a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)‖ ≤
      ‖a n * z^(2*n)‖ := by
  have hn : ‖(Real.sqrt (1-u^2) : ℂ)‖^(2*n) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (sonine_sqrt_norm_le_one u hu)
  calc
    ‖a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)‖ =
        (‖a n‖ * ‖z‖^(2*n)) *
          ‖(Real.sqrt (1-u^2) : ℂ)‖^(2*n) := by
            simp [mul_pow, norm_mul, norm_pow, mul_assoc]
    _ ≤ (‖a n‖ * ‖z‖^(2*n)) * 1 :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖a n * z^(2*n)‖ := by
      simp [norm_mul, norm_pow]

/-- Dominated convergence on the actual interval for the actual
    complex even Taylor series at a fixed complex parameter. -/
theorem sonine_interval_hasSum (a : ℕ → ℂ) (z : ℂ)
    (h : Summable (fun n : ℕ => ‖a n * z^(2*n)‖)) :
    HasSum
      (fun n : ℕ => ∫ u in (-1 : ℝ)..1,
        a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))
      (∫ u in (-1 : ℝ)..1,
        ∑' n : ℕ, a n *
          (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => ‖a n * z^(2*n)‖)
  · intro n
    have hc : Continuous (fun u : ℝ =>
        a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)) := by fun_prop
    exact hc.aestronglyMeasurable
  · intro n
    filter_upwards with u
    intro hu
    exact sonine_integrand_norm_le a z n u (uIoc_subset_uIcc hu)
  · filter_upwards with u
    intro _
    exact h
  · exact intervalIntegrable_const
  · filter_upwards with u
    intro hu
    exact (h.of_norm_bounded
      (fun n => sonine_integrand_norm_le a z n u (uIoc_subset_uIcc hu))).hasSum

#print axioms Manuscript14Sonine.sonine_interval_hasSum

end Manuscript14Sonine
