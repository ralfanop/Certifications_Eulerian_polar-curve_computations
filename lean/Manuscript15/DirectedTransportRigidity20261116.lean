import Manuscript15.Section27PrimalWasserstein

/-! M15 §8, eq:directed-transport-exact. The infimum is over actual
probability-measure couplings, with actual marginal first moments. -/
open MeasureTheory
noncomputable section
namespace Manuscript15.LipschitzExtensions
open Manuscript15.Section27.Primal

def directed (l : ℝ) (x y : ℝ) : ℝ :=
  l * max (y-x) 0 + max (x-y) 0

theorem directed_pointwise (l x y : ℝ) :
    directed l x y = (l+1)/2 * |x-y| + (l-1)/2 * (y-x) := by
  unfold directed
  by_cases h : x ≤ y
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
        abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' : y ≤ x := le_of_not_ge h
    rw [max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h'),
        abs_of_nonneg (sub_nonneg.mpr h')]
    ring

def directedCost (l : ℝ) (γ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ p, directed l p.1 p.2 ∂γ

def directedW (l : ℝ) (μ ν : Measure ℝ) : ℝ :=
  sInf (directedCost l '' couplings μ ν)

theorem directedCost_eq (l : ℝ) {μ ν : Measure ℝ} {γ : Measure (ℝ × ℝ)}
    (hγ : γ ∈ couplings μ ν)
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    directedCost l γ = (l+1)/2 * cost γ +
      (l-1)/2 * ((∫ y, y ∂ν) - ∫ x, x ∂μ) := by
  have hc := cost_integrable hγ hμ hν
  change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
  have hp : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
  have hq : MeasurePreserving Prod.snd γ ν := ⟨measurable_snd, hγ.2⟩
  have hx : Integrable (fun p : ℝ × ℝ => p.1) γ := hp.integrable_comp_of_integrable hμ
  have hy : Integrable (fun p : ℝ × ℝ => p.2) γ := hq.integrable_comp_of_integrable hν
  have hix : (∫ p : ℝ × ℝ, p.1 ∂γ) = ∫ x, x ∂μ := by
    have hm : AEStronglyMeasurable (fun x : ℝ => x) (Measure.map Prod.fst γ) := by
      rw [hγ.1]; exact hμ.aestronglyMeasurable
    rw [← integral_map measurable_fst.aemeasurable hm, hγ.1]
  have hiy : (∫ p : ℝ × ℝ, p.2 ∂γ) = ∫ y, y ∂ν := by
    have hm : AEStronglyMeasurable (fun x : ℝ => x) (Measure.map Prod.snd γ) := by
      rw [hγ.2]; exact hν.aestronglyMeasurable
    rw [← integral_map measurable_snd.aemeasurable hm, hγ.2]
  unfold directedCost
  calc
    _ = ∫ p : ℝ × ℝ, (l+1)/2 * |p.1-p.2| + (l-1)/2 * (p.2-p.1) ∂γ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => directed_pointwise l p.1 p.2)
    _ = _ := by
      rw [integral_add (hc.const_mul _) ((hy.sub' hx).const_mul _),
        integral_const_mul, integral_const_mul, integral_sub hy hx, hiy, hix]
      rfl

theorem directedW_eq (l : ℝ) (hl : 0 < l)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    directedW l μ ν = (l+1)/2 * wasserstein1 μ ν +
      (l-1)/2 * ((∫ y, y ∂ν) - ∫ x, x ∂μ) := by
  let A := (l+1)/2
  let b := (l-1)/2 * ((∫ y, y ∂ν) - ∫ x, x ∂μ)
  have hA : 0 < A := by dsimp [A]; linarith
  have he : ∀ γ ∈ couplings μ ν, directedCost l γ = A * cost γ + b :=
    fun γ hγ => directedCost_eq l hγ hμ hν
  have hn := couplings_nonempty μ ν
  have hb : BddBelow (cost '' couplings μ ν) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨γ, _, rfl⟩
    exact integral_nonneg (fun p => abs_nonneg (p.1-p.2))
  have hd : BddBelow (directedCost l '' couplings μ ν) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨γ, _, rfl⟩
    apply integral_nonneg
    intro p
    unfold directed
    exact add_nonneg (mul_nonneg hl.le (le_max_right _ _)) (le_max_right _ _)
  change directedW l μ ν = A * wasserstein1 μ ν + b
  apply le_antisymm
  · have hi : (directedW l μ ν - b)/A ≤ wasserstein1 μ ν := by
      unfold wasserstein1
      apply le_csInf (hn.image cost)
      rintro _ ⟨γ, hγ, rfl⟩
      have h := csInf_le hd (Set.mem_image_of_mem (directedCost l) hγ)
      change directedW l μ ν ≤ directedCost l γ at h
      rw [he γ hγ] at h
      apply (div_le_iff₀ hA).2
      linarith [mul_comm A (cost γ)]
    have h := (div_le_iff₀ hA).1 hi
    linarith [mul_comm (wasserstein1 μ ν) A]
  · unfold directedW
    apply le_csInf (hn.image (directedCost l))
    rintro _ ⟨γ, hγ, rfl⟩
    rw [he γ hγ]
    change A * sInf (cost '' couplings μ ν) + b ≤ A * cost γ + b
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (csInf_le hb (Set.mem_image_of_mem cost hγ)) hA.le) b

theorem directedW_same_mean (l : ℝ) (hl : 0 < l)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν)
    (hm : (∫ x, x ∂μ) = ∫ y, y ∂ν) :
    directedW l μ ν = (l+1)/2 * wasserstein1 μ ν := by
  rw [directedW_eq l hl μ ν hμ hν, hm, sub_self, mul_zero, add_zero]

end Manuscript15.LipschitzExtensions
#print axioms Manuscript15.LipschitzExtensions.directed_pointwise
#print axioms Manuscript15.LipschitzExtensions.directedCost_eq
#print axioms Manuscript15.LipschitzExtensions.directedW_eq
#print axioms Manuscript15.LipschitzExtensions.directedW_same_mean
