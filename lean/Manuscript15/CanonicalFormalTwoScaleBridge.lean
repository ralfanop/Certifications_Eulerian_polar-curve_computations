import Manuscript15.FormalTwoScaleRecurrence
import Manuscript15.CoefficientExistence

/-!
# Manuscript 15 — canonical rigidity sequence forced by the true formal two-scale equation

The independently established full two-scale coefficient recurrence
  (2n+3)4^(n+1)c_(n+1) = -(1/2) Σ_{j=0}^n c_j c_(n-j),
  c₀=1
admits an explicit canonical real sequence of all orders from well-founded
recursion (CoefficientExistence). The exact FORMAL power-series equation
  1-G(4u)-2u(d/du)G(4u) = (u/2)G(u)^2
rigorously implies this coefficient rule (FormalTwoScaleRecurrence).

Therefore, any formal solution necessarily equals the same canonical
sequence at EVERY coefficient, and there can be at most one such formal
solution. The algebraic recurrence solution exists independently, but
the converse assertion that its formal series satisfies the formal
equation is a separate proof obligation, not assumed here.

This does not claim analytic convergence or uniqueness of a probability
measure or analytic characteristic function.
-/

noncomputable section

namespace Manuscript15

/-- Any REAL formal two-scale differential-equation solution
is precisely the canonical all-order rigidity coefficient sequence. -/
theorem formalTwoScaleEquation_eq_canonical
    (c : ℕ → ℝ) (h : FormalTwoScaleEquation c) :
    c = rigidityCoefficientSequence := by
  exact coefficientRule_eq_canonical c
    (formalTwoScaleEquation_implies_coefficientRule c h)

/-- The canonical algebraic coefficient sequence is the unique possible
formal solution: any actual formal two-scale solution equals it. -/
theorem formalTwoScaleEquation_solution_unique_if_exists :
    ∀ c : ℕ → ℝ, FormalTwoScaleEquation c →
      c = rigidityCoefficientSequence := by
  intro c h
  exact formalTwoScaleEquation_eq_canonical c h

/-- The first four canonical coefficient values are fixed exactly
by the recurrence, with no analytic existence assumption. -/
theorem rigidityCoefficientSequence_first_values :
    rigidityCoefficientSequence 0 = 1 ∧
      rigidityCoefficientSequence 1 = -(1 / 24 : ℝ) ∧
      rigidityCoefficientSequence 2 = (1 / 1920 : ℝ) ∧
      rigidityCoefficientSequence 3 = -(1 / 322560 : ℝ) := by
  have hc := rigidityCoefficientSequence_rule
  exact ⟨hc.1,
    coefficientRule_c_one rigidityCoefficientSequence hc,
    coefficientRule_c_two rigidityCoefficientSequence hc,
    coefficientRule_c_three rigidityCoefficientSequence hc⟩

#print axioms Manuscript15.formalTwoScaleEquation_eq_canonical
#print axioms Manuscript15.formalTwoScaleEquation_solution_unique_if_exists
#print axioms Manuscript15.rigidityCoefficientSequence_first_values

end Manuscript15
