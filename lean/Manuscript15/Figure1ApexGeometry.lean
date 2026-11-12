/-
Manuscript 15, Figure 1: exact n=3 Eulerian histogram coordinates
and elementary apex slope/half-angle geometry.

The figure's original 7000 profiles remain unchanged. These lemmas
concern only the exact outer n=3 profile, not its rendered arc placement.
-/
import EulerianCert.Bracket
import Mathlib

open Real
noncomputable section
namespace Manuscript15

/-- The actual Eulerian-number row for n=3 in the certified inherited
    recurrence is exactly [1,4,1]. -/
theorem eulerian_n3_numbers :
    EulerianCert.Bracket.E 3 0 = 1 ∧
    EulerianCert.Bracket.E 3 1 = 4 ∧
    EulerianCert.Bracket.E 3 2 = 1 := by
  decide +kernel

/-- The three n=3 probabilities sum to one exactly. -/
theorem eulerian_n3_probability_mass :
    (1 / 6 : ℝ) + 2 / 3 + 1 / 6 = 1 := by
  norm_num

/-- The outer n=3 histogram has left slope +2 in *isometric*
    coordinates x=k/(n+1), y=E(n,k-1)/n!. -/
theorem eulerian_n3_left_slope :
    ((2 / 3 : ℝ) - 1 / 6) / (1 / 2 - 1 / 4) = 2 := by
  norm_num

/-- Corresponding right slope is -2, by reflection symmetry. -/
theorem eulerian_n3_right_slope :
    ((1 / 6 : ℝ) - 2 / 3) / (3 / 4 - 1 / 2) = -2 := by
  norm_num

/-- The two downward-pointing side vectors at the n=3 apex,
    (-1,-2) and (1,-2), have dot product 3 and norm² 5 each. -/
theorem eulerian_n3_apex_vector_data :
    (-1 : ℝ) * 1 + (-2) * (-2) = 3 ∧
    (-1 : ℝ) ^ 2 + (-2) ^ 2 = 5 ∧
    (1 : ℝ) ^ 2 + (-2) ^ 2 = 5 := by
  norm_num

/-- The cosine of the apex angle is the rational 3/5; positive,
    so the angle is acute. The fraction is dimensionless. -/
theorem eulerian_n3_apex_cosine_quotient :
    ((-1 : ℝ) * 1 + (-2) * (-2)) / 5 = 3 / 5 := by
  norm_num

noncomputable def alphaThree : ℝ := 2 * Real.arctan (1 / 2)

/-- Exact half-angle tangent, compatible with the apex slope ±2. -/
theorem eulerian_n3_tan_half_angle :
    Real.tan (alphaThree / 2) = 1 / 2 := by
  unfold alphaThree
  have hs : (2 * Real.arctan (1 / 2)) / 2 =
      Real.arctan (1 / 2) := by ring
  rw [hs, Real.tan_arctan]

#print axioms Manuscript15.eulerian_n3_numbers
#print axioms Manuscript15.eulerian_n3_probability_mass
#print axioms Manuscript15.eulerian_n3_left_slope
#print axioms Manuscript15.eulerian_n3_right_slope
#print axioms Manuscript15.eulerian_n3_apex_vector_data
#print axioms Manuscript15.eulerian_n3_apex_cosine_quotient
#print axioms Manuscript15.eulerian_n3_tan_half_angle

end Manuscript15
