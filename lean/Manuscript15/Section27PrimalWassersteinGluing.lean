import Manuscript15.Section27PrimalWasserstein

/-!
# M15 §2.7 — Borel gluing and primal Wasserstein-1 triangle inequality

Disintegrate the second coupling over its first marginal and extend the
first coupling using the resulting conditional Markov kernel. This yields
a genuine measure on triples, with the required pairwise pushforwards.
No optimal transport plan or Kantorovich duality is assumed.
-/

open MeasureTheory ProbabilityTheory
noncomputable section

namespace Manuscript15.Section27.Primal

private abbrev Triple := (ℝ × ℝ) × ℝ

private def yz (p : Triple) : ℝ × ℝ := (p.1.2, p.2)
private def xz (p : Triple) : ℝ × ℝ := (p.1.1, p.2)

private theorem yz_measurable : Measurable yz := by
  unfold yz
  fun_prop

private theorem xz_measurable : Measurable xz := by
  unfold xz
  fun_prop

theorem coupling_isProbability {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    {γ : Measure (ℝ × ℝ)} (hγ : γ ∈ couplings μ ν) :
    IsProbabilityMeasure γ := by
  change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
  constructor
  have h := congrArg (fun m : Measure ℝ => m Set.univ) hγ.1
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
  exact h.trans (measure_univ (μ := μ))

/-- The gluing lemma for finite Borel measures on pairs of reals. -/
theorem glue_pair_measures (γ δ : Measure (ℝ × ℝ))
    [IsFiniteMeasure γ] [IsFiniteMeasure δ]
    (h : Measure.map Prod.snd γ = Measure.map Prod.fst δ) :
    ∃ η : Measure Triple,
      Measure.map Prod.fst η = γ ∧ Measure.map yz η = δ := by
  let κ : Kernel (ℝ × ℝ) ℝ := δ.condKernel.comap Prod.snd measurable_snd
  letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  refine ⟨γ.compProd κ, ?_, ?_⟩
  · exact Measure.fst_compProd γ κ
  · apply Measure.ext
    intro s hs
    have hm : Measurable (fun y : ℝ => (δ.condKernel y) (Prod.mk y ⁻¹' s)) :=
      Kernel.measurable_kernel_prodMk_left hs
    calc
      (Measure.map yz (γ.compProd κ)) s =
          ∫⁻ p : ℝ × ℝ, (δ.condKernel p.2) (Prod.mk p.2 ⁻¹' s) ∂γ := by
        rw [Measure.map_apply yz_measurable hs,
          Measure.compProd_apply (yz_measurable hs)] <;> rfl
      _ = ∫⁻ y : ℝ, (δ.condKernel y) (Prod.mk y ⁻¹' s)
          ∂Measure.map Prod.snd γ := (lintegral_map hm measurable_snd).symm
      _ = ∫⁻ y : ℝ, (δ.condKernel y) (Prod.mk y ⁻¹' s) ∂δ.fst := by
        rw [h] <;> rfl
      _ = δ s := by
        rw [← Measure.compProd_apply hs, Measure.disintegrate δ δ.condKernel]

/-- Glue two admissible couplings and bound the cost of their endpoint
coupling by the sum of the two original costs. -/
theorem coupling_cost_triangle
    {μ ν ρ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {γ δ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν) (hδ : δ ∈ couplings ν ρ)
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν)
    (hρ : Integrable (fun x : ℝ => x) ρ) :
    ∃ θ ∈ couplings μ ρ, cost θ ≤ cost γ + cost δ := by
  have hcγ := cost_integrable hγ hμ hν
  have hcδ := cost_integrable hδ hν hρ
  letI : IsProbabilityMeasure γ := coupling_isProbability hγ
  letI : IsProbabilityMeasure δ := coupling_isProbability hδ
  change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
  change Measure.map Prod.fst δ = ν ∧ Measure.map Prod.snd δ = ρ at hδ
  obtain ⟨η, hxy, hyz⟩ := glue_pair_measures γ δ (hγ.2.trans hδ.1.symm)
  let θ := Measure.map xz η
  have hθ : θ ∈ couplings μ ρ := by
    change Measure.map Prod.fst θ = μ ∧ Measure.map Prod.snd θ = ρ
    constructor
    · calc
        Measure.map Prod.fst θ = Measure.map Prod.fst (Measure.map Prod.fst η) := by
          dsimp [θ]
          rw [Measure.map_map measurable_fst xz_measurable,
            Measure.map_map measurable_fst measurable_fst] <;> rfl
        _ = μ := by rw [hxy, hγ.1]
    · calc
        Measure.map Prod.snd θ = Measure.map Prod.snd (Measure.map yz η) := by
          dsimp [θ]
          rw [Measure.map_map measurable_snd xz_measurable,
            Measure.map_map measurable_snd yz_measurable] <;> rfl
        _ = ρ := by rw [hyz, hδ.2]
  refine ⟨θ, hθ, ?_⟩
  have hcθ := cost_integrable hθ hμ hρ
  have hA : MeasurePreserving Prod.fst η γ := ⟨measurable_fst, hxy⟩
  have hB : MeasurePreserving yz η δ := ⟨yz_measurable, hyz⟩
  have hC : MeasurePreserving xz η θ := ⟨xz_measurable, rfl⟩
  have h1 : Integrable (fun p : Triple => |p.1.1 - p.1.2|) η :=
    hA.integrable_comp_of_integrable hcγ
  have h2 : Integrable (fun p : Triple => |p.1.2 - p.2|) η :=
    hB.integrable_comp_of_integrable hcδ
  have h3 : Integrable (fun p : Triple => |p.1.1 - p.2|) η :=
    hC.integrable_comp_of_integrable hcθ
  have heq {f : Triple → ℝ} {g : ℝ × ℝ → ℝ} {π : Triple → ℝ × ℝ}
      {τ : Measure (ℝ × ℝ)} (hp : MeasurePreserving π η τ)
      (hg : Integrable g τ) (hf : f = fun p => g (π p)) :
      (∫ p, f p ∂η) = ∫ z, g z ∂τ := by
    have hm : AEStronglyMeasurable g (Measure.map π η) := by
      rw [hp.map_eq]
      exact hg.aestronglyMeasurable
    rw [hf, ← integral_map hp.measurable.aemeasurable hm, hp.map_eq]
  calc
    cost θ = ∫ p : Triple, |p.1.1 - p.2| ∂η :=
      (heq hC hcθ rfl).symm
    _ ≤ ∫ p : Triple, (|p.1.1 - p.1.2| + |p.1.2 - p.2|) ∂η := by
      apply integral_mono h3 (h1.add h2)
      intro p
      exact abs_sub_le p.1.1 p.1.2 p.2
    _ = cost γ + cost δ := by
      have e1 : (∫ p : Triple, |p.1.1 - p.1.2| ∂η) = cost γ :=
        heq hA hcγ rfl
      have e2 : (∫ p : Triple, |p.1.2 - p.2| ∂η) = cost δ :=
        heq hB hcδ rfl
      rw [integral_add h1 h2, e1, e2]

private theorem cost_inf_le {μ ν : Measure ℝ} {γ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν) : wasserstein1 μ ν ≤ cost γ := by
  have hb : BddBelow (cost '' couplings μ ν) := by
    refine ⟨0, ?_⟩
    intro c hc
    obtain ⟨γ', _, rfl⟩ := hc
    exact integral_nonneg (fun p => abs_nonneg (p.1 - p.2))
  exact csInf_le hb ⟨γ, hγ, rfl⟩

theorem exists_near_optimal_coupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ ∈ couplings μ ν, cost γ < wasserstein1 μ ν + ε := by
  have h : sInf (cost '' couplings μ ν) < wasserstein1 μ ν + ε := by
    change wasserstein1 μ ν < wasserstein1 μ ν + ε
    linarith
  obtain ⟨c, ⟨γ, hγ, rfl⟩, hc⟩ :=
    exists_lt_of_csInf_lt ((couplings_nonempty μ ν).image cost) h
  exact ⟨γ, hγ, hc⟩

/-- Genuine triangle inequality on the finite-first-moment probability
domain, obtained by gluing almost-minimizers. -/
theorem wasserstein1_triangle (μ ν ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν)
    (hρ : Integrable (fun x : ℝ => x) ρ) :
    wasserstein1 μ ρ ≤ wasserstein1 μ ν + wasserstein1 ν ρ := by
  by_contra! h
  let ε := (wasserstein1 μ ρ - (wasserstein1 μ ν + wasserstein1 ν ρ)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨γ, hγ, hcγ⟩ := exists_near_optimal_coupling μ ν hε
  obtain ⟨δ, hδ, hcδ⟩ := exists_near_optimal_coupling ν ρ hε
  obtain ⟨θ, hθ, hcθ⟩ := coupling_cost_triangle hγ hδ hμ hν hρ
  have hbound := cost_inf_le hθ
  dsimp [ε] at hcγ hcδ
  linarith

#print axioms Manuscript15.Section27.Primal.coupling_isProbability
#print axioms Manuscript15.Section27.Primal.glue_pair_measures
#print axioms Manuscript15.Section27.Primal.coupling_cost_triangle
#print axioms Manuscript15.Section27.Primal.exists_near_optimal_coupling
#print axioms Manuscript15.Section27.Primal.wasserstein1_triangle

end Manuscript15.Section27.Primal
