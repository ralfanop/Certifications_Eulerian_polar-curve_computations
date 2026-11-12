import Manuscript15.UniformLawMomentsCharacteristic
import Mathlib

/-!
# Manuscript 15 — exact fourth and sixth cumulants of the genuine centered uniform law

These statements use the actual Borel probability measure
`centredUniformLaw = cond volume (Icc (-1/2) (1/2))`.
They are derived exclusively from previously compiled exact Lebesgue
moment identities and do not invoke formal or truncated approximations.

All formulas are for a centered law; its first and third moments vanish.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory

/-- The actual centered uniform law has strictly positive variance. -/
theorem centredUniformLaw_variance_pos :
    (0 : ℝ) < (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) := by
  rw [centredUniformLaw_second_moment]
  norm_num

/-- Exact standardized fourth raw moment (kurtosis) of the actual law. -/
theorem centredUniformLaw_standardized_fourth_moment :
    (∫ x : ℝ, x ^ 4 ∂centredUniformLaw) /
      (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) ^ 2 = (9 / 5 : ℝ) := by
  rw [centredUniformLaw_fourth_moment, centredUniformLaw_second_moment]
  norm_num

/-- Exact standardized fourth cumulant (excess kurtosis) equals -6/5. -/
theorem centredUniformLaw_excess_kurtosis :
    ((∫ x : ℝ, x ^ 4 ∂centredUniformLaw) -
      3 * (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) ^ 2) /
        (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) ^ 2 = -(6 / 5 : ℝ) := by
  rw [centredUniformLaw_fourth_moment, centredUniformLaw_second_moment]
  norm_num

/-- The *sixth cumulant* of the genuine centered uniform probability
law is positive and exactly 1/252. The full centered sixth-cumulant
formula includes the cubic moment term (which vanishes here). -/
theorem centredUniformLaw_sixth_cumulant :
    (∫ x : ℝ, x ^ 6 ∂centredUniformLaw) -
      15 * (∫ x : ℝ, x ^ 4 ∂centredUniformLaw) *
        (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) -
      10 * (∫ x : ℝ, x ^ 3 ∂centredUniformLaw) ^ 2 +
      30 * (∫ x : ℝ, x ^ 2 ∂centredUniformLaw) ^ 3 =
        (1 / 252 : ℝ) := by
  rw [centredUniformLaw_sixth_moment, centredUniformLaw_fourth_moment,
    centredUniformLaw_third_moment, centredUniformLaw_second_moment]
  norm_num

#print axioms Manuscript15.centredUniformLaw_variance_pos
#print axioms Manuscript15.centredUniformLaw_standardized_fourth_moment
#print axioms Manuscript15.centredUniformLaw_excess_kurtosis
#print axioms Manuscript15.centredUniformLaw_sixth_cumulant

end Manuscript15
