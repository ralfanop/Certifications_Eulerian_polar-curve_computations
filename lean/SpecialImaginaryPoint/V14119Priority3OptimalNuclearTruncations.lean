import SpecialImaginaryPoint.V14119Priority3OptimalNuclearMass

/-!
# Priority 3: norm-controlled finite nuclear truncations

This module makes the optimal-mass polar representation from the
kernel-certified Priority 3 optimal nuclear cost theorem quantitative
at the level of all finite partial sums.

For an arbitrary complex CFC Schatten-S₁ Hilbert operator T, one
single nuclear presentation T = ∑'ᵢ |uᵢ⟩⟨vᵢ| has exactly optimal
mass ∑'ᵢ ‖uᵢ‖ ‖vᵢ‖ = ‖T‖₁, and EVERY finite truncation satisfies
‖∑_{i∈s} |uᵢ⟩⟨vᵢ|‖₁ ≤ ‖T‖₁.

The finite truncations converge to T in the actual CFC trace norm.
This uniform control will be an input to the finite-rank determinant
perturbation estimate; it does not prove that determinant estimate.
-/

noncomputable section

namespace Manuscript14Priority3.NuclearRankOne

open Filter Topology
open Manuscript14Priority3.TraceClassModel

/-- A finite sum of genuine CFC-S₁ rank-one maps is bounded in
the genuine CFC trace norm by its finite nuclear mass. -/
theorem nuclear_finset_traceNorm_le_mass {ι : Type*}
    (s : Finset ι) (u v : ι → H) :
    ‖∑ i ∈ s, rankOneS1 (u i) (v i)‖ ≤
      ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
  calc
    ‖∑ i ∈ s, rankOneS1 (u i) (v i)‖ ≤
        ∑ i ∈ s, ‖rankOneS1 (u i) (v i)‖ := by
      exact norm_sum_le _ _
    _ = ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
      simp only [rankOneS1_norm_eq]

/-- Each arbitrary CFC-S₁ operator has a fixed optimal nuclear
representation whose finite truncations are uniformly controlled
by the true trace norm of the target and converge to it in S₁.
No positivity, normality or diagonality assumption is imposed. -/
theorem traceClass_exists_optimal_normControlled_truncations
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (u v : w → H),
      Summable (fun i : w => ‖u i‖ * ‖v i‖) ∧
      (∑' i : w, rankOneS1 (u i) (v i)) = T ∧
      (∑' i : w, ‖u i‖ * ‖v i‖) = ‖T‖ ∧
      (∀ s : Finset w,
        ‖∑ i ∈ s, rankOneS1 (u i) (v i)‖ ≤ ‖T‖) ∧
      Tendsto
        (fun s : Finset w => ∑ i ∈ s, rankOneS1 (u i) (v i))
        atTop (𝓝 T) := by
  obtain ⟨w, c, u, v, hcost, hT, hmass⟩ :=
    traceClass_exists_optimal_nuclear_representation T
  refine ⟨w, u, v, hcost, hT, hmass, ?_, ?_⟩
  · intro s
    calc
      ‖∑ i ∈ s, rankOneS1 (u i) (v i)‖ ≤
          ∑ i ∈ s, ‖u i‖ * ‖v i‖ :=
        nuclear_finset_traceNorm_le_mass s u v
      _ ≤ ∑' i : w, ‖u i‖ * ‖v i‖ := by
        exact hcost.sum_le_tsum s (fun i hi => by positivity)
      _ = ‖T‖ := hmass
  · have hterms :
        Summable (fun i : w => rankOneS1 (u i) (v i)) := by
      apply Summable.of_norm
      exact hcost.congr
        (fun i => (rankOneS1_norm_eq (u i) (v i)).symm)
    rw [← hT]
    exact hterms.hasSum

#print axioms Manuscript14Priority3.NuclearRankOne.nuclear_finset_traceNorm_le_mass
#print axioms Manuscript14Priority3.NuclearRankOne.traceClass_exists_optimal_normControlled_truncations

end Manuscript14Priority3.NuclearRankOne
