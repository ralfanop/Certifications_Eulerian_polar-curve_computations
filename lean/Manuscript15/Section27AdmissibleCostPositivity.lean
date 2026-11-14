import Manuscript15.Section27AdmissibleMeasureCosts

/-!
# M15 §2.7 — positivity of admissible integral transport costs

The previous coupling-cost infimum estimates apply to real-valued
integral costs. Here nonnegativity of the underlying pointwise cost
provides a uniform lower bound on all admissible integral costs,
independently of whether a Wasserstein metric is yet identified.

Classical consequences of nonnegative Lebesgue integrals and order
completeness; no originality claim.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- Every integral cost in a nonempty admissible measure family is
nonnegative whenever the pointwise transport cost is nonnegative. -/
theorem admissible_integral_costs_nonnegative
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (cost : Ω → ℝ)
    (hcost : ∀ ω, 0 ≤ cost ω) :
    ∀ c ∈ ((fun μ : Measure Ω => ∫ ω, cost ω ∂μ) '' admissible), 0 ≤ c := by
  intro c hc
  rcases hc with ⟨μ, hμ, rfl⟩
  exact integral_nonneg hcost

/-- The infimum of the actual admissible integral costs is nonnegative.
The nonempty-family assumption is explicit, as is necessary for a
finite real sInf to be the correct transport cost infimum. -/
theorem nonneg_infimum_admissible_measure_costs
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (cost : Ω → ℝ)
    (hne : admissible.Nonempty)
    (hcost : ∀ ω, 0 ≤ cost ω) :
    0 ≤ sInf ((fun μ : Measure Ω => ∫ ω, cost ω ∂μ) '' admissible) := by
  apply le_csInf
  · rcases hne with ⟨μ, hμ⟩
    exact ⟨∫ ω, cost ω ∂μ, ⟨μ, hμ, rfl⟩⟩
  · exact admissible_integral_costs_nonnegative admissible cost hcost

#print axioms Manuscript15.Section27.admissible_integral_costs_nonnegative
#print axioms Manuscript15.Section27.nonneg_infimum_admissible_measure_costs

end Manuscript15.Section27
