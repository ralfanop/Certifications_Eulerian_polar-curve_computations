import Manuscript15.FormalTwoScaleRecurrence
import Manuscript15.RationalRigiditySequence

/-!
# Manuscript 15 — every coefficient of any formal two-scale solution is rational

Combining the exact formal coefficient-extraction theorem with the
all-order canonical recurrence and its rationality over ℚ, this
module proves:

For every real formal power series G satisfying
  1-G(4u)-2u(d/du)G(4u) = (u/2) G(u)^2,
EVERY Taylor coefficient c_n of G is exactly rational, with no
truncation and no numerical approximation.

This is a conditional formal-algebraic theorem. It does NOT assert
that any particular entire characteristic function or probability
measure satisfies the equation. Existence of an analytic realization
and an associated probability measure remain separate obligations.
-/

noncomputable section

namespace Manuscript15

/-- All-order exact rationality of every REAL coefficient of any
formal solution to the full cycloidal two-scale differential equation. -/
theorem formalTwoScaleEquation_all_coefficients_rational
    (c : ℕ → ℝ) (hc : FormalTwoScaleEquation c)
    (n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = c n := by
  have hcanonical : c = rigidityCoefficientSequence :=
    coefficientRule_eq_canonical c
      (formalTwoScaleEquation_implies_coefficientRule c hc)
  obtain ⟨q, hq⟩ := rigidityCoefficientSequence_all_rational n
  refine ⟨q, ?_⟩
  rw [hcanonical]
  exact hq

#print axioms Manuscript15.formalTwoScaleEquation_all_coefficients_rational

end Manuscript15
