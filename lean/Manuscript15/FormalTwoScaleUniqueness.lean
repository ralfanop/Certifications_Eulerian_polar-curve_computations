import Manuscript15.FormalTwoScaleRecurrence

/-!
# Manuscript 15 — formal two-scale Eulerian cycloidal uniqueness

For a REAL formal power series G(u) = Σ_n c_n u^n, consider
  1 - G(4u) - 2u G'(4u) = (u/2) G(u)^2,
where the derivative is with respect to u of the already rescaled
power series. This module establishes that the exact formal equation
has AT MOST ONE solution (in the coefficient sequence representation).

The proof uses the earlier formal coefficient-extraction theorem
and the independently kernel-audited triangular recurrence
uniqueness. It does NOT assert that a formal solution exists,
nor that the eventual sequence converges analytically.
-/

noncomputable section

namespace Manuscript15

/-- Two real formal coefficient sequences satisfying the ACTUAL
two-scale formal differential equation are pointwise identical. -/
theorem formalTwoScaleEquation_unique
    (c d : ℕ → ℝ)
    (hc : FormalTwoScaleEquation c)
    (hd : FormalTwoScaleEquation d) :
    c = d := by
  exact coefficientRule_unique c d
    (formalTwoScaleEquation_implies_coefficientRule c hc)
    (formalTwoScaleEquation_implies_coefficientRule d hd)

/-- The initial coefficient of any genuine FORMAL two-scale
differential-equation solution is exactly 1. -/
theorem formalTwoScaleEquation_c_zero
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) :
    c 0 = 1 :=
  (formalTwoScaleEquation_implies_coefficientRule c hc).1

/-- Every genuine formal two-scale equation solution has
the exact rational coefficient c₁ = -1/24. -/
theorem formalTwoScaleEquation_c_one
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) :
    c 1 = -(1 / 24 : ℝ) :=
  coefficientRule_c_one c (formalTwoScaleEquation_implies_coefficientRule c hc)

/-- Every genuine formal two-scale equation solution has
the exact rational coefficient c₂ = 1/1920. -/
theorem formalTwoScaleEquation_c_two
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) :
    c 2 = (1 / 1920 : ℝ) :=
  coefficientRule_c_two c (formalTwoScaleEquation_implies_coefficientRule c hc)

/-- Every genuine formal two-scale equation solution has
the exact rational coefficient c₃ = -1/322560. -/
theorem formalTwoScaleEquation_c_three
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) :
    c 3 = -(1 / 322560 : ℝ) :=
  coefficientRule_c_three c (formalTwoScaleEquation_implies_coefficientRule c hc)

#print axioms Manuscript15.formalTwoScaleEquation_unique
#print axioms Manuscript15.formalTwoScaleEquation_c_zero
#print axioms Manuscript15.formalTwoScaleEquation_c_one
#print axioms Manuscript15.formalTwoScaleEquation_c_two
#print axioms Manuscript15.formalTwoScaleEquation_c_three

end Manuscript15
