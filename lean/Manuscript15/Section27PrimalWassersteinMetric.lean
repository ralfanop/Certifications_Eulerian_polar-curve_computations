import Manuscript15.Section27PrimalWasserstein

/-!
# M15 §2.7 — metric properties of primal Wasserstein-1

Diagonal and transposed pushforward couplings, and the resulting identity
and symmetry properties of the actual primal infimum. The triangle
inequality is not asserted here: it requires a gluing argument.
-/

open MeasureTheory
noncomputable section

namespace Manuscript15.Section27.Primal

theorem cost_nonneg (γ : Measure (ℝ × ℝ)) : 0 ≤ cost γ :=
  integral_nonneg (fun p => abs_nonneg (p.1 - p.2))

theorem cost_set_bddBelow (μ ν : Measure ℝ) : BddBelow (cost '' couplings μ ν) := by
  refine ⟨0, ?_⟩
  intro t ht
  obtain ⟨γ, _, rfl⟩ := ht
  exact cost_nonneg γ

theorem wasserstein1_le_cost {μ ν : Measure ℝ} {γ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν) : wasserstein1 μ ν ≤ cost γ := by
  unfold wasserstein1
  exact csInf_le (cost_set_bddBelow μ ν) ⟨γ, hγ, rfl⟩

def diagonalMeasure (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun x : ℝ => (x, x)) μ

theorem diagonal_mem (μ : Measure ℝ) : diagonalMeasure μ ∈ couplings μ μ := by
  have hd : Measurable (fun x : ℝ => (x, x)) := by fun_prop
  change Measure.map Prod.fst (diagonalMeasure μ) = μ ∧
    Measure.map Prod.snd (diagonalMeasure μ) = μ
  constructor
  · rw [diagonalMeasure, Measure.map_map measurable_fst hd]
    simp [Function.comp_def]
  · rw [diagonalMeasure, Measure.map_map measurable_snd hd]
    simp [Function.comp_def]

theorem diagonal_cost (μ : Measure ℝ) : cost (diagonalMeasure μ) = 0 := by
  have hd : Measurable (fun x : ℝ => (x, x)) := by fun_prop
  have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p.2|) := by fun_prop
  unfold cost diagonalMeasure
  rw [integral_map hd.aemeasurable hc.aestronglyMeasurable]
  simp

theorem wasserstein1_self (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    wasserstein1 μ μ = 0 := by
  apply le_antisymm _ (wasserstein1_nonneg μ μ)
  simpa only [diagonal_cost] using wasserstein1_le_cost (diagonal_mem μ)

def swapCoupling (γ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  Measure.map (fun p : ℝ × ℝ => (p.2, p.1)) γ

theorem swap_mem {μ ν : Measure ℝ} {γ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν) : swapCoupling γ ∈ couplings ν μ := by
  change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
  have hs : Measurable (fun p : ℝ × ℝ => (p.2, p.1)) := by fun_prop
  change Measure.map Prod.fst (swapCoupling γ) = ν ∧
    Measure.map Prod.snd (swapCoupling γ) = μ
  constructor
  · rw [swapCoupling, Measure.map_map measurable_fst hs]
    simpa only [Function.comp_def] using hγ.2
  · rw [swapCoupling, Measure.map_map measurable_snd hs]
    simpa only [Function.comp_def] using hγ.1

theorem swap_cost (γ : Measure (ℝ × ℝ)) : cost (swapCoupling γ) = cost γ := by
  have hs : Measurable (fun p : ℝ × ℝ => (p.2, p.1)) := by fun_prop
  have hc : Continuous (fun p : ℝ × ℝ => |p.1 - p.2|) := by fun_prop
  unfold cost swapCoupling
  rw [integral_map hs.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => abs_sub_comm p.2 p.1)

theorem wasserstein1_symm (μ ν : Measure ℝ) :
    wasserstein1 μ ν = wasserstein1 ν μ := by
  have h : cost '' couplings μ ν = cost '' couplings ν μ := by
    ext r
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨swapCoupling γ, swap_mem hγ, swap_cost γ⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨swapCoupling γ, swap_mem hγ, swap_cost γ⟩
  unfold wasserstein1
  rw [h]

theorem wasserstein1_eq_zero_iff (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    wasserstein1 μ ν = 0 ↔ μ = ν := by
  constructor
  · exact eq_of_wasserstein1_eq_zero μ ν hμ hν
  · intro h
    subst ν
    exact wasserstein1_self μ

#print axioms Manuscript15.Section27.Primal.cost_nonneg
#print axioms Manuscript15.Section27.Primal.cost_set_bddBelow
#print axioms Manuscript15.Section27.Primal.wasserstein1_le_cost
#print axioms Manuscript15.Section27.Primal.diagonal_mem
#print axioms Manuscript15.Section27.Primal.diagonal_cost
#print axioms Manuscript15.Section27.Primal.wasserstein1_self
#print axioms Manuscript15.Section27.Primal.swap_mem
#print axioms Manuscript15.Section27.Primal.swap_cost
#print axioms Manuscript15.Section27.Primal.wasserstein1_symm
#print axioms Manuscript15.Section27.Primal.wasserstein1_eq_zero_iff

end Manuscript15.Section27.Primal
