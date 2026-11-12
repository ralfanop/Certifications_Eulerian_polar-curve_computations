/-
Manuscript 15 — genuine measure-level Eulerian characteristic function.

A prior Mathlib proof defines a normalized Borel probability law:
  μ_E = cond volume (Icc (-1/2) (1/2)).
Other separately kernel-checked proofs evaluate the interval cosine
transform and exact uniform moments.

This integration step proves that the actual law's real characteristic
function and moments equal those formulas, not merely formal analogues.
It deliberately does not claim uniqueness among all probability laws.
-/
import Manuscript15.UniformProbabilityLaw
import Manuscript15.UniformCosineIntegral
import Manuscript15.UniformMoments
import Mathlib

open Real MeasureTheory
noncomputable section
namespace Manuscript15

/-- Because the supporting interval has Lebesgue mass exactly one,
    conditional probability agrees with its restricted volume measure. -/
theorem centredUniformLaw_eq_restrict :
    centredUniformLaw =
      (volume : Measure ℝ).restrict unitCentredInterval := by
  unfold centredUniformLaw ProbabilityTheory.cond
  rw [unitCentredInterval_volume]
  simp

/-- Integrating any real measurable formula against the uniform law
    is precisely a restricted real Lebesgue integral. -/
theorem centredUniformLaw_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂centredUniformLaw) =
      (∫ x in unitCentredInterval, f x) := by
  rw [centredUniformLaw_eq_restrict]
  rfl

/-- Genuine probability expectation equals an oriented intervalIntegral
    because singleton endpoints have zero Lebesgue measure. -/
theorem centredUniformLaw_interval_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂centredUniformLaw) =
      (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f x) := by
  rw [centredUniformLaw_integral]
  unfold unitCentredInterval
  rw [integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]

/-- The actual centred-uniform probability law has precisely the
    original Eulerian sinc as its *real cosine* characteristic function. -/
theorem centredUniformLaw_cosine_characteristic (t : ℝ) :
    (∫ x, Real.cos (t * x) ∂centredUniformLaw) =
      EulerianCert.FourierModes.rE t := by
  rw [centredUniformLaw_interval_integral]
  exact uniform_cosine_eq_eulerian t

/-- The sine (imaginary) part of the centred-uniform characteristic
    transform vanishes by exact symmetry. -/
theorem centredUniformLaw_sine_characteristic (t : ℝ) :
    (∫ x, Real.sin (t * x) ∂centredUniformLaw) = 0 := by
  rw [centredUniformLaw_interval_integral]
  exact uniform_sine_integral_zero t

/-- Exact centred mean, now against an actual probability measure. -/
theorem centredUniformLaw_first_moment :
    (∫ x, x ^ 1 ∂centredUniformLaw) = 0 := by
  rw [centredUniformLaw_interval_integral]
  simpa only [neg_div] using centred_uniform_first_moment

/-- Exact variance raw moment of the actual probability law. -/
theorem centredUniformLaw_second_moment :
    (∫ x, x ^ 2 ∂centredUniformLaw) = 1 / 12 := by
  rw [centredUniformLaw_interval_integral]
  simpa only [neg_div] using centred_uniform_second_moment

/-- Exact fourth raw moment of the actual probability law. -/
theorem centredUniformLaw_fourth_moment :
    (∫ x, x ^ 4 ∂centredUniformLaw) = 1 / 80 := by
  rw [centredUniformLaw_interval_integral]
  simpa only [neg_div] using centred_uniform_fourth_moment

/-- Exact sixth raw moment of the actual probability law. -/
theorem centredUniformLaw_sixth_moment :
    (∫ x, x ^ 6 ∂centredUniformLaw) = 1 / 448 := by
  rw [centredUniformLaw_interval_integral]
  simpa only [neg_div] using centred_uniform_sixth_moment

#print axioms Manuscript15.centredUniformLaw_eq_restrict
#print axioms Manuscript15.centredUniformLaw_integral
#print axioms Manuscript15.centredUniformLaw_interval_integral
#print axioms Manuscript15.centredUniformLaw_cosine_characteristic
#print axioms Manuscript15.centredUniformLaw_sine_characteristic
#print axioms Manuscript15.centredUniformLaw_first_moment
#print axioms Manuscript15.centredUniformLaw_second_moment
#print axioms Manuscript15.centredUniformLaw_fourth_moment
#print axioms Manuscript15.centredUniformLaw_sixth_moment

end Manuscript15
