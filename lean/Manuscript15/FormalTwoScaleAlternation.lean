import Manuscript15.FormalTwoScaleRecurrence
import Manuscript15.CoefficientAlternation

/-!
# Manuscript 15 — every formal two-scale solution has strictly alternating nonzero coefficients

Mathlib PowerSeries coefficient extraction from the genuine
cycloidal two-scale formal functional differential equation provides
the exact all-order recurrence CoefficientRule. Independently,
the recurrence implies a STRICT sign alternation and nonvanishing
at EVERY natural-number index.

This module closes the formal-algebraic bridge: any complete formal
two-scale solution has nonzero strictly alternating coefficients.
This is a universal structural statement, not a finite coefficient
calculation, and does not assert analytic convergence or existence
of a corresponding probability measure.
-/

noncomputable section

namespace Manuscript15

/-- Every coefficient of ANY exact formal two-scale cycloidal
differential-equation solution is nonzero with strict alternating sign. -/
theorem formalTwoScaleEquation_all_orders_strict_alternation
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * c n :=
  coefficientRule_all_orders_strict_alternation c
    (formalTwoScaleEquation_implies_coefficientRule c hc) n

/-- In particular, NONE of the infinitely many coefficients of
an exact formal two-scale solution vanishes. -/
theorem formalTwoScaleEquation_all_orders_ne_zero
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c) (n : ℕ) :
    c n ≠ 0 :=
  coefficientRule_all_orders_ne_zero c
    (formalTwoScaleEquation_implies_coefficientRule c hc) n

#print axioms Manuscript15.formalTwoScaleEquation_all_orders_strict_alternation
#print axioms Manuscript15.formalTwoScaleEquation_all_orders_ne_zero

end Manuscript15
