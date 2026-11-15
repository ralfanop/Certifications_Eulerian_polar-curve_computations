import Mathlib

/-!
Manuscript 16 v16.4, Section 13, Proposition mixed-schatten-164:
exact scalar Neumann margin for the off-diagonal bounded perturbation.

These lemmas DO NOT prove operator invertibility, graph-domain equality,
the Neumann series in Banach spaces, compactness or Schatten membership.
-/

namespace Manuscript16

/-- A norm bound strictly below 3/2 gives a positive resolvent gap. -/
theorem v164_neumann_gap_pos (e : ℝ) (he : e < 3 / 2) :
    0 < 3 / 2 - e := by
  linarith

/-- The Neumann ratio (2/3)e is strictly less than one. -/
theorem v164_neumann_ratio_lt_one (e : ℝ) (he : e < 3 / 2) :
    (2 / 3 : ℝ) * e < 1 := by
  linarith

/-- Exact scalar reduction of the Neumann-series upper bound to
    the published denominator (3/2 - ||E||). -/
theorem v164_neumann_bound_scalar_identity (e : ℝ)
    (he : e < 3 / 2) :
    ((2 / 3 : ℝ) / (1 - (2 / 3 : ℝ) * e)) =
      1 / (3 / 2 - e) := by
  have hgap : (3 / 2 : ℝ) - e ≠ 0 := ne_of_gt (v164_neumann_gap_pos e he)
  have hmargin : (1 : ℝ) - (2 / 3 : ℝ) * e ≠ 0 := by
    have h := v164_neumann_ratio_lt_one e he
    linarith
  field_simp
  <;> ring

/-- The numerical upper bound is positive under the stated hypothesis. -/
theorem v164_neumann_bound_pos (e : ℝ) (he : e < 3 / 2) :
    0 < (1 : ℝ) / (3 / 2 - e) := by
  exact one_div_pos.mpr (v164_neumann_gap_pos e he)

#print axioms Manuscript16.v164_neumann_gap_pos
#print axioms Manuscript16.v164_neumann_ratio_lt_one
#print axioms Manuscript16.v164_neumann_bound_scalar_identity
#print axioms Manuscript16.v164_neumann_bound_pos

end Manuscript16
