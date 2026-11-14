import Manuscript15.Section27AdmissibleCostPositivity

/-!
# M15 §2.7 — zero transport-cost normalization

An exact boundary case for the admissible-measure cost infimum.
The nonemptiness hypothesis is essential: over the reals, the infimum
of the empty set is not a transport distance. This lemma does not
assert that admissible measures have prescribed marginals.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- The infimum of zero integral costs over a nonempty family of
measures equals zero. -/
theorem zero_cost_infimum_of_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (admissible : Set (Measure Ω))
    (hne : admissible.Nonempty) :
    sInf ((fun μ : Measure Ω => ∫ _ω, (0 : ℝ) ∂μ) '' admissible) = 0 := by
  have himage :
      ((fun μ : Measure Ω => ∫ _ω, (0 : ℝ) ∂μ) '' admissible) = {0} := by
    ext x
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      simp
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      rcases hne with ⟨μ, hμ⟩
      exact ⟨μ, hμ, by simp⟩
  rw [himage]
  simp

#print axioms Manuscript15.Section27.zero_cost_infimum_of_nonempty

end Manuscript15.Section27
