import GegenbauerFock.UltrasphericalGammaDensity
import Mathlib

/-!
# V007 — exact normalized uniform-law realization of the λ=1/2 measure

The Eulerian member of the symmetric Beta-pushforward ultraspherical
probability measure has exactly the constant Lebesgue density 1/2 on
(-1,1), with zero extension. This is an equality of actual Mathlib
measure values, not merely a matching sequence of moments.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- The genuine Eulerian uniform density, extended by zero on ℝ. -/
noncomputable def eulerianUniformDensity (u : ℝ) : ℝ :=
  if -1 < u ∧ u < 1 then 1 / 2 else 0

private theorem realGamma_half_eq_sqrt_pi :
    Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := by
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 2 : ℝ)
  norm_num [Real.Gamma_one] at hdup
  simpa using hdup

private theorem realGamma_three_halves_eq_sqrt_pi_half :
    Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
  calc
    Real.Gamma (3 / 2 : ℝ) =
        Real.Gamma ((1 / 2 : ℝ) + 1) := by congr 1 <;> norm_num
    _ = (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) :=
      Real.Gamma_add_one (by norm_num)
    _ = Real.sqrt Real.pi / 2 := by
      rw [realGamma_half_eq_sqrt_pi]
      ring

/-- Exact pointwise density at every real u, including endpoint zeroes. -/
theorem gammaDensity_half_eq_eulerianUniformDensity (u : ℝ) :
    gammaDensity (1 / 2) u = eulerianUniformDensity u := by
  by_cases hu : -1 < u ∧ u < 1
  · unfold gammaDensity eulerianUniformDensity
    rw [if_pos hu, if_pos hu]
    have hs : (1 / 2 : ℝ) - 1 / 2 = 0 := by norm_num
    have hshape : shape (1 / 2 : ℝ) = 1 := by
      norm_num [shape]
    have hgamarg : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
    rw [hs, Real.rpow_zero, mul_one, hshape, hgamarg,
      realGamma_three_halves_eq_sqrt_pi_half, Real.Gamma_one]
    have hp : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    field_simp
  · simp only [gammaDensity, eulerianUniformDensity, if_neg hu]

/-- Equality of actual ultraspherical and uniform-Lebesgue probability
measures on ℝ, not merely of moments or characteristic functions. -/
theorem measure_half_eq_uniformDensity :
    measure (1 / 2) =
      (volume : Measure ℝ).withDensity
        (fun u : ℝ => ENNReal.ofReal (eulerianUniformDensity u)) := by
  rw [measure_eq_withDensity_gamma (1 / 2) (by norm_num)]
  congr 1
  funext u
  rw [gammaDensity_half_eq_eulerianUniformDensity]

/-- Consequently every Bochner-integrable real observation against the
Eulerian ultraspherical law can be rewritten against the normalized
Lebesgue density on (-1,1). -/
theorem integral_measure_half_eq_uniformDensity (f : ℝ → ℝ) :
    (∫ u : ℝ, f u ∂(measure (1 / 2))) =
      ∫ u : ℝ, f u ∂((volume : Measure ℝ).withDensity
        (fun v : ℝ => ENNReal.ofReal (eulerianUniformDensity v))) := by
  rw [measure_half_eq_uniformDensity]

#print axioms GegenbauerFock.Ultraspherical.gammaDensity_half_eq_eulerianUniformDensity
#print axioms GegenbauerFock.Ultraspherical.measure_half_eq_uniformDensity
#print axioms GegenbauerFock.Ultraspherical.integral_measure_half_eq_uniformDensity

end GegenbauerFock.Ultraspherical
