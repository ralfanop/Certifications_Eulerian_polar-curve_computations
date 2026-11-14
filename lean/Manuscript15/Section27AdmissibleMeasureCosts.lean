import Manuscript15.Section27CostInfimum

/-!
# Manuscript 15 §2.7 — indexed admissible coupling costs

An explicit family of genuine measures and their Bochner-integral costs
is converted into the set of admissible costs whose infimum controls a
single fixed discrepancy. This closes the *indexed measure -> cost set*
step left abstract by Section27CostInfimum, without claiming the measures
are couplings with prescribed marginals or that this is Mathlib's W₁.

The proof combines classical norm-of-integral domination with the
order-theoretic infimum lemma. Neither result is claimed as original.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- For any nonempty collection of measures, if the same real discrepancy
is bounded by the cost integral for every admissible measure, then it is
bounded by the infimum of their actual integral costs. -/
theorem discrepancy_le_infimum_admissible_measure_integrals
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (cost : Ω → ℝ) (discrepancy : ℝ)
    (hne : admissible.Nonempty)
    (hbound : ∀ μ ∈ admissible,
      discrepancy ≤ ∫ ω, cost ω ∂μ) :
    discrepancy ≤
      sInf ((fun μ : Measure Ω => ∫ ω, cost ω ∂μ) '' admissible) := by
  let costs : Set ℝ :=
    (fun μ : Measure Ω => ∫ ω, cost ω ∂μ) '' admissible
  have hcosts : costs.Nonempty := by
    rcases hne with ⟨μ, hμ⟩
    exact ⟨∫ ω, cost ω ∂μ, ⟨μ, hμ, rfl⟩⟩
  have hcostbound : ∀ c ∈ costs, discrepancy ≤ c := by
    intro c hc
    rcases hc with ⟨μ, hμ, rfl⟩
    exact hbound μ hμ
  exact discrepancy_le_coupling_cost_infimum costs discrepancy hcosts hcostbound

/-- The previous indexed-infimum theorem with the integral transport
inequality supplied by the actual measure-level theorem. Assumptions
explicitly require integrability for *each* admissible measure. -/
theorem integral_discrepancy_le_infimum_admissible_measure_costs
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (f g cost : Ω → ℝ) (discrepancy : ℝ)
    (hne : admissible.Nonempty)
    (hf : ∀ μ ∈ admissible, Integrable f μ)
    (hg : ∀ μ ∈ admissible, Integrable g μ)
    (hc : ∀ μ ∈ admissible, Integrable cost μ)
    (hpoint : ∀ ω, |f ω - g ω| ≤ cost ω)
    (hdiscrepancy : ∀ μ ∈ admissible,
      discrepancy ≤ |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)|) :
    discrepancy ≤
      sInf ((fun μ : Measure Ω => ∫ ω, cost ω ∂μ) '' admissible) := by
  apply discrepancy_le_infimum_admissible_measure_integrals
    admissible cost discrepancy hne
  intro μ hμ
  calc
    discrepancy ≤
        |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| :=
      hdiscrepancy μ hμ
    _ ≤ ∫ ω, cost ω ∂μ :=
      integral_transport_of_pointwise_bound μ f g cost
        (hf μ hμ) (hg μ hμ) (hc μ hμ) hpoint

#print axioms Manuscript15.Section27.discrepancy_le_infimum_admissible_measure_integrals
#print axioms Manuscript15.Section27.integral_discrepancy_le_infimum_admissible_measure_costs

end Manuscript15.Section27
