import Mathlib

/-!
# Manuscript 15 §2.7: abstract coupling-cost infimum bridge

This is an order-theoretic step only. The hypotheses do not yet identify
the admissible set with couplings having prescribed marginals, or identify
its infimum with Mathlib's Wasserstein-1 distance.
-/

namespace Manuscript15.Section27

/-- A bound valid for every admissible cost passes to its infimum,
provided the admissible cost set is nonempty. -/
theorem bound_le_admissible_cost_infimum
    (costs : Set ℝ) (d : ℝ)
    (hne : costs.Nonempty)
    (hbound : ∀ c ∈ costs, d ≤ c) :
    d ≤ sInf costs := by
  exact le_csInf hne hbound

/-- The same order step when costs are indexed by admissible witnesses. -/
theorem bound_le_witness_cost_infimum
    {α : Type*} (admissible : Set α) (cost : α → ℝ) (d : ℝ)
    (hne : admissible.Nonempty)
    (hbound : ∀ a ∈ admissible, d ≤ cost a) :
    d ≤ sInf (cost '' admissible) := by
  apply le_csInf (hne.image cost)
  intro c hc
  rcases hc with ⟨a, ha, rfl⟩
  exact hbound a ha

#print axioms Manuscript15.Section27.bound_le_admissible_cost_infimum
#print axioms Manuscript15.Section27.bound_le_witness_cost_infimum

end Manuscript15.Section27
