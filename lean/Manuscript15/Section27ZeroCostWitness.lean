import Manuscript15.Section27AdmissibleCostPositivity

/-!
# M15 §2.7 — zero-cost witness and the admissible integral infimum

For a nonempty family of actual measures and a pointwise nonnegative
real cost, one admissible measure with zero integral forces the infimum
of all admissible integral costs to equal zero.

This is a transport-cost normalization lemma, not an identification
with Wasserstein-1 or a proof of prescribed marginals.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- A single admissible zero-cost witness forces the nonnegative
admissible integral-cost infimum to vanish. -/
theorem infimum_eq_zero_of_admissible_zero_witness
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (cost : Ω → ℝ)
    (hcost : ∀ ω, 0 ≤ cost ω)
    (μ : Measure Ω)
    (hμ : μ ∈ admissible)
    (hzero : (∫ ω, cost ω ∂μ) = 0) :
    sInf ((fun ν : Measure Ω => ∫ ω, cost ω ∂ν) '' admissible) = 0 := by
  have hne : admissible.Nonempty := ⟨μ, hμ⟩
  have hnonneg :=
    nonneg_infimum_admissible_measure_costs admissible cost hne hcost
  have hbelow :
      BddBelow ((fun ν : Measure Ω => ∫ ω, cost ω ∂ν) '' admissible) := by
    refine ⟨0, ?_⟩
    exact admissible_integral_costs_nonnegative admissible cost hcost
  have hupper :
      sInf ((fun ν : Measure Ω => ∫ ω, cost ω ∂ν) '' admissible) ≤ 0 := by
    apply csInf_le hbelow
    exact ⟨μ, hμ, hzero⟩
  exact le_antisymm hupper hnonneg

#print axioms Manuscript15.Section27.infimum_eq_zero_of_admissible_zero_witness

end Manuscript15.Section27
