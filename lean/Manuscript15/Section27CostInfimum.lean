import Manuscript15.Section27WeightedCoordinate

/-!
# Manuscript 15 §2.7 — abstract coupling-cost infimum step

This is the order-theoretic passage from bounds valid for *every*
admissible coupling cost to the infimum of those costs. It does not
identify the set with Mathlib's Wasserstein distance, nor establish
marginal pushforward identities or a reconstruction theorem.
-/

namespace Manuscript15.Section27

/-- If a real discrepancy is bounded by every admissible coupling cost,
it is bounded by the infimum of the nonempty cost set. -/
theorem discrepancy_le_coupling_cost_infimum
    (costs : Set ℝ) (discrepancy : ℝ)
    (hnonempty : costs.Nonempty)
    (hbound : ∀ c ∈ costs, discrepancy ≤ c) :
    discrepancy ≤ sInf costs := by
  exact le_csInf hnonempty hbound

/-- The same order-theoretic step for the set of scaled costs. This
deliberately avoids claiming that scaling commutes with infimum without
the additional nonnegativity and nonemptiness hypotheses. -/
theorem discrepancy_le_scaled_coupling_cost_infimum
    (scaledCosts : Set ℝ) (discrepancy : ℝ)
    (hnonempty : scaledCosts.Nonempty)
    (hbound : ∀ c ∈ scaledCosts, discrepancy ≤ c) :
    discrepancy ≤ sInf scaledCosts := by
  exact le_csInf hnonempty hbound

#print axioms Manuscript15.Section27.discrepancy_le_coupling_cost_infimum
#print axioms Manuscript15.Section27.discrepancy_le_scaled_coupling_cost_infimum

end Manuscript15.Section27
