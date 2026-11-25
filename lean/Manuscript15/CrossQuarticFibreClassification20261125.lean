import Manuscript15.CrossQuarticCurve20261125
import Mathlib

/-!
# M15 §10: EXHAUSTIVE affine fibres of the degree-two quartic map

Source: Manuscript_15_20261125_CROSS_CONNECTIONS(1).zip, Proposition
10.2, eq:cross-curveZ, eq:cross-curveW and eq:cross-curveTarget.

The preceding certified module establishes the two distinct
source points (t,Y), (-1/t,Y/t²), their source-curve equations,
and equality of their exact rational images. This module proves
the converse: for each generic real affine source point with t≠0
and t²≠1, ANY affine point (s,U), s²≠1, with the same two
target coordinates equals one of those two points.

This is the precise real affine fibre cardinality result needed
for the algebraic degree-two assertion. It does NOT assert the
existence or degree of the extension to smooth projective curves,
nor does it assume an elliptic-curve structure.
-/

namespace Manuscript15.CrossQuarticFibreClassification20261125

open Manuscript15.CrossQuartic20261125

/-- The equality of the actual rational z-coordinates forces
either coincident source parameters or the companion relation
s*t=-1. This proves exhaustivity rather than just existence. -/
theorem quarticZ_equal_implies_two_parameters (s t : ℝ)
    (hs : 1 - s ^ 2 ≠ 0) (ht : 1 - t ^ 2 ≠ 0)
    (hz : quarticZ s = quarticZ t) :
    s = t ∨ s * t = -1 := by
  have hroot : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  unfold quarticZ at hz
  have hcross :
      (Real.sqrt (2 : ℝ) * s) * (1 - t ^ 2) =
        (Real.sqrt (2 : ℝ) * t) * (1 - s ^ 2) :=
    (div_eq_div_iff hs ht).mp hz
  have hfactor :
      Real.sqrt (2 : ℝ) * ((s - t) * (1 + s * t)) = 0 := by
    calc
      Real.sqrt (2 : ℝ) * ((s - t) * (1 + s * t)) =
          (Real.sqrt (2 : ℝ) * s) * (1 - t ^ 2) -
            (Real.sqrt (2 : ℝ) * t) * (1 - s ^ 2) := by ring
      _ = 0 := sub_eq_zero.mpr hcross
  have hprod : (s - t) * (1 + s * t) = 0 := by
    rcases mul_eq_zero.mp hfactor with hbad | hgood
    · exact False.elim (hroot hbad)
    · exact hgood
  rcases mul_eq_zero.mp hprod with hsame | hcomp
  · exact Or.inl (sub_eq_zero.mp hsame)
  · exact Or.inr (by linarith)

/-- At every admissible source parameter t the W map is
injective in its actual Y coordinate, by a positive scalar
coefficient. No source-curve equation is needed. -/
theorem quarticW_injective_in_Y (t Y U : ℝ)
    (ht : 1 - t ^ 2 ≠ 0)
    (hW : quarticW t U = quarticW t Y) :
    U = Y := by
  have hden : (1 - t ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnum : 1 + t ^ 2 ≠ 0 := by positivity
  unfold quarticW at hW
  have hcleared :
      ((1 + t ^ 2) * U) * (1 - t ^ 2) ^ 2 =
        ((1 + t ^ 2) * Y) * (1 - t ^ 2) ^ 2 :=
    (div_eq_div_iff hden hden).mp hW
  have hlinear : (1 + t ^ 2) * U = (1 + t ^ 2) * Y :=
    (mul_right_cancel₀ hden) hcleared
  exact (mul_left_cancel₀ hnum) hlinear

/-- EXHAUSTIVE two-point classification of the entire affine
fibre of the actual map (z,W) at a generic real point.
Both source components are fixed, not only the quadratic
parameter t. The two points are proved distinct elsewhere. -/
theorem generic_affine_fibre_exactly_two
    (t Y s U : ℝ)
    (ht : t ≠ 0)
    (hdt : 1 - t ^ 2 ≠ 0)
    (hds : 1 - s ^ 2 ≠ 0)
    (hz : quarticZ s = quarticZ t)
    (hw : quarticW s U = quarticW t Y) :
    (s = t ∧ U = Y) ∨
      (s = -1 / t ∧ U = Y / t ^ 2) := by
  rcases quarticZ_equal_implies_two_parameters s t hds hdt hz with hsame | hcomp
  · subst s
    left
    exact ⟨rfl, quarticW_injective_in_Y t Y U hdt hw⟩
  · have hs : s = -1 / t := by
      apply (eq_div_iff ht).2
      exact hcomp
    have hcompW := quarticW_companion t Y ht hdt
    have hU : U = Y / t ^ 2 :=
      quarticW_injective_in_Y (-1 / t) (Y / t ^ 2) U
        (companion_denominator_nonzero t ht hdt)
        (by simpa only [← hs] using hw.trans hcompW.symm)
    exact Or.inr ⟨hs, hU⟩

#print axioms Manuscript15.CrossQuarticFibreClassification20261125.quarticZ_equal_implies_two_parameters
#print axioms Manuscript15.CrossQuarticFibreClassification20261125.quarticW_injective_in_Y
#print axioms Manuscript15.CrossQuarticFibreClassification20261125.generic_affine_fibre_exactly_two

end Manuscript15.CrossQuarticFibreClassification20261125
