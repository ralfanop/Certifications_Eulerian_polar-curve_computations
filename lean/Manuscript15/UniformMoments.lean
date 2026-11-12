/-
Manuscript 15 — exact Lebesgue moments of the centred uniform law.

Every integral is a literal intervalIntegral, not a substituted
rational constant. The interval [-1/2,1/2] has total mass 1.
These proofs supply the moment values used by the manuscript's
fourth-order cusp and uniform-convolution formulas.

They do not assert independence, existence of a probability measure
instance, or a probabilistic convolution theorem.
-/
import Mathlib

open Real MeasureTheory
noncomputable section
namespace Manuscript15

theorem centred_uniform_mass :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), (1 : ℝ)) = 1 := by
  norm_num

theorem centred_uniform_first_moment :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), x ^ 1) = 0 := by
  rw [integral_pow]
  norm_num

theorem centred_uniform_second_moment :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), x ^ 2) = 1 / 12 := by
  rw [integral_pow]
  norm_num

theorem centred_uniform_third_moment :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), x ^ 3) = 0 := by
  rw [integral_pow]
  norm_num

theorem centred_uniform_fourth_moment :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), x ^ 4) = 1 / 80 := by
  rw [integral_pow]
  norm_num

theorem centred_uniform_sixth_moment :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), x ^ 6) = 1 / 448 := by
  rw [integral_pow]
  norm_num

/-- The exact fourth cumulant is negative, -1/120, for the uniform law. -/
theorem centred_uniform_fourth_cumulant :
    (1 / 80 : ℝ) - 3 * (1 / 12 : ℝ) ^ 2 = -(1 / 120 : ℝ) := by
  norm_num

#print axioms Manuscript15.centred_uniform_mass
#print axioms Manuscript15.centred_uniform_first_moment
#print axioms Manuscript15.centred_uniform_second_moment
#print axioms Manuscript15.centred_uniform_third_moment
#print axioms Manuscript15.centred_uniform_fourth_moment
#print axioms Manuscript15.centred_uniform_sixth_moment
#print axioms Manuscript15.centred_uniform_fourth_cumulant

end Manuscript15
