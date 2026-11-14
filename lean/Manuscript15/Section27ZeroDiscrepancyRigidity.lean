import Manuscript15.Section27ZeroCostNormalization

/-!
# M15 §2.7 — zero-cost rigidity of nonnegative discrepancies

If a nonnegative discrepancy is bounded by the infimum of zero
integral costs over a nonempty family of actual measures, it vanishes.
This is a boundary-case consequence of the zero-cost normalization,
not an identification of the admissible family with Wasserstein couplings.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- A nonnegative discrepancy controlled by the zero-cost infimum
over a nonempty admissible measure family is identically zero. -/
theorem discrepancy_eq_zero_of_zero_cost_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (discrepancy : ℝ)
    (hne : admissible.Nonempty)
    (hnonneg : 0 ≤ discrepancy)
    (hbound :
      discrepancy ≤
        sInf ((fun μ : Measure Ω => ∫ _ω, (0 : ℝ) ∂μ) '' admissible)) :
    discrepancy = 0 := by
  have hzero :
      sInf ((fun μ : Measure Ω => ∫ _ω, (0 : ℝ) ∂μ) '' admissible) = 0 :=
    zero_cost_infimum_of_nonempty admissible hne
  exact le_antisymm (hzero ▸ hbound) hnonneg

#print axioms Manuscript15.Section27.discrepancy_eq_zero_of_zero_cost_bound

end Manuscript15.Section27
