import Manuscript15.MagneticGibbsGraphPrimalBridge20261117

/-! M15 §8.4: concrete odd-lattice rounding, its exact cells and
pushforward atom masses. The first-moment primal theorem is for an
actual probability law and its rounding pushforward, before
identifying the exponential density with the geometric Gibbs law. -/

open MeasureTheory
noncomputable section

namespace Manuscript15.MagneticGibbs.Rounding
open Manuscript15.Section27.Primal
open Manuscript15.MagneticGibbs

def roundEnergy (E : ℝ) : ℝ := oddLevel ⌊E / 2⌋

theorem measurable_roundEnergy : Measurable roundEnergy := by
  exact (measurable_of_countable oddLevel).comp
    (Int.measurable_floor.comp (measurable_id.div_const 2))

theorem round_cell (E : ℝ) :
    2 * (⌊E / 2⌋ : ℝ) ≤ E ∧ E < 2 * (⌊E / 2⌋ : ℝ) + 2 := by
  constructor
  · linarith [Int.floor_le (E / 2)]
  · linarith [Int.lt_floor_add_one (E / 2)]

theorem round_nearest (E : ℝ) (j : ℤ) :
    |E - roundEnergy E| ≤ |E - oddLevel j| := by
  exact odd_cell_nearest E ⌊E / 2⌋ j (round_cell E).1 (round_cell E).2.le

theorem round_displacement_le_one (E : ℝ) : |E - roundEnergy E| ≤ 1 := by
  exact cell_displacement_le_one E ⌊E / 2⌋ (round_cell E).1 (round_cell E).2.le

theorem round_preimage_cell (k : ℤ) :
    roundEnergy ⁻¹' {oddLevel k} = Set.Ico (2 * (k : ℝ)) (2 * (k : ℝ) + 2) := by
  ext E
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
  constructor
  · intro he
    have hc : (⌊E / 2⌋ : ℝ) = (k : ℝ) := by
      unfold roundEnergy oddLevel at he
      linarith
    have hi : ⌊E / 2⌋ = k := by exact_mod_cast hc
    have hb := Int.floor_eq_iff.mp hi
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · intro he
    have hi : ⌊E / 2⌋ = k :=
      Int.floor_eq_iff.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    simp only [roundEnergy, hi]

theorem round_atom_mass (μ : Measure ℝ) (k : ℤ) :
    Measure.map roundEnergy μ {oddLevel k} =
      μ (Set.Ico (2 * (k : ℝ)) (2 * (k : ℝ) + 2)) := by
  rw [Measure.map_apply measurable_roundEnergy (measurableSet_singleton _),
    round_preimage_cell]

/-- Every coupling to the rounding law is supported, in its second
coordinate, on the odd integer lattice. -/
theorem coupling_odd_ae (μ : Measure ℝ) (γ : Measure (ℝ × ℝ))
    (hγ : γ ∈ couplings μ (Measure.map roundEnergy μ)) :
    ∀ᵐ p ∂γ, p.2 ∈ Set.range oddLevel := by
  have hs : MeasurableSet (Set.range oddLevel) :=
    (Set.countable_range oddLevel).measurableSet
  have ht : ∀ᵐ y ∂(Measure.map roundEnergy μ), y ∈ Set.range oddLevel :=
    (ae_map_iff measurable_roundEnergy.aemeasurable hs).2
      (Filter.Eventually.of_forall fun E => ⟨⌊E / 2⌋, rfl⟩)
  have hm : Measure.map Prod.snd γ = Measure.map roundEnergy μ := hγ.2
  rw [← hm] at ht
  exact (ae_map_iff measurable_snd.aemeasurable hs).1 ht

theorem coupling_nearest_ae (μ : Measure ℝ) (γ : Measure (ℝ × ℝ))
    (hγ : γ ∈ couplings μ (Measure.map roundEnergy μ)) :
    ∀ᵐ p ∂γ, |p.1 - roundEnergy p.1| ≤ |p.1 - p.2| := by
  filter_upwards [coupling_odd_ae μ γ hγ] with p hp
  obtain ⟨j, hj⟩ := hp
  rw [← hj]
  exact round_nearest p.1 j

theorem graph_cost_eq_ae (μ : Measure ℝ) :
    ∀ᵐ p ∂(Measure.map (fun E : ℝ => (E, roundEnergy E)) μ),
      |p.1 - p.2| = |p.1 - roundEnergy p.1| := by
  let f : ℝ × ℝ → ℝ := fun p => |p.1 - p.2|
  let g : ℝ × ℝ → ℝ := fun p => |p.1 - roundEnergy p.1|
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := (measurable_fst.sub
    (measurable_roundEnergy.comp measurable_fst)).abs
  have hs : MeasurableSet {p | f p = g p} := by
    have he : {p | f p = g p} = {p | f p ≤ g p} ∩ {p | g p ≤ f p} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, le_antisymm_iff]
    rw [he]
    exact (measurableSet_le hf hg).inter (measurableSet_le hg hf)
  have hmap : Measurable (fun E : ℝ => (E, roundEnergy E)) :=
    measurable_id.prodMk measurable_roundEnergy
  change ∀ᵐ p ∂(Measure.map (fun E : ℝ => (E, roundEnergy E)) μ), f p = g p
  exact (ae_map_iff hmap.aemeasurable hs).2 (Filter.Eventually.of_forall fun _ => rfl)

/-- Genuine W1 optimum for a probability measure and its odd rounding law.
The exponential-law identification and evaluation of the integral remain
separate; no optimal-transport duality is postulated. -/
theorem round_wasserstein1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) :
    wasserstein1 μ (Measure.map roundEnergy μ) =
      ∫ x, |x - roundEnergy x| ∂μ := by
  have hi : Integrable roundEnergy μ := by
    apply (hμ.norm.add (integrable_const (1 : ℝ))).mono'
      measurable_roundEnergy.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro E
    simp only [Real.norm_eq_abs]
    calc
      |roundEnergy E| = |(roundEnergy E - E) + E| := by congr 1 <;> ring
      _ ≤ |roundEnergy E - E| + |E| := abs_add_le _ _
      _ ≤ |E| + 1 := by linarith [round_displacement_le_one E, abs_sub_comm (roundEnergy E) E]
  have hν : Integrable (fun x : ℝ => x) (Measure.map roundEnergy μ) := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_roundEnergy.aemeasurable).2
    exact hi
  have hm : Integrable (fun x : ℝ => |x - roundEnergy x|) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_id.sub measurable_roundEnergy).abs.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact round_displacement_le_one x
  exact Manuscript15.MagneticGibbs.GraphPrimalBridge.graph_primal_infimum
    μ roundEnergy measurable_roundEnergy (fun p => |p.1 - p.2|)
    (fun x => |x - roundEnergy x|) hm
    (fun γ hγ => cost_integrable hγ hμ hν)
    (coupling_nearest_ae μ) (graph_cost_eq_ae μ)

end Manuscript15.MagneticGibbs.Rounding

#print axioms Manuscript15.MagneticGibbs.Rounding.measurable_roundEnergy
#print axioms Manuscript15.MagneticGibbs.Rounding.round_cell
#print axioms Manuscript15.MagneticGibbs.Rounding.round_nearest
#print axioms Manuscript15.MagneticGibbs.Rounding.round_displacement_le_one
#print axioms Manuscript15.MagneticGibbs.Rounding.round_preimage_cell
#print axioms Manuscript15.MagneticGibbs.Rounding.round_atom_mass
#print axioms Manuscript15.MagneticGibbs.Rounding.coupling_odd_ae
#print axioms Manuscript15.MagneticGibbs.Rounding.coupling_nearest_ae
#print axioms Manuscript15.MagneticGibbs.Rounding.graph_cost_eq_ae
#print axioms Manuscript15.MagneticGibbs.Rounding.round_wasserstein1
