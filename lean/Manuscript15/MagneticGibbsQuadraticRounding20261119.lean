import Manuscript15.MagneticGibbsRounding20261117

/-! M15 §8.4: genuine primal quadratic optimality of odd-lattice rounding.
Unlike the already audited W1 lemma, this establishes the finite second
moment of the rounded law and minimizes actual squared costs over ALL
couplings. Evaluation for the exponential Gibbs law is a separate gate. -/

open MeasureTheory
noncomputable section
namespace Manuscript15.MagneticGibbs.Rounding
open Manuscript15.Section27.Primal

def wasserstein2Squared (μ ν : Measure ℝ) : ℝ :=
  sInf ((fun γ : Measure (ℝ × ℝ) => ∫ p, (p.1 - p.2)^2 ∂γ) '' couplings μ ν)

theorem rounded_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x^2) μ) :
    Integrable (fun x : ℝ => x^2) (Measure.map roundEnergy μ) := by
  apply (integrable_map_measure (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => x^2) (Measure.map roundEnergy μ))
    measurable_roundEnergy.aemeasurable).2
  have hi : Integrable (fun x : ℝ => 2*x^2+2) μ :=
    (hμ.const_mul 2).add (integrable_const 2)
  apply hi.mono'
    (by
      exact (measurable_roundEnergy.pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := round_displacement_le_one x
  have hn := abs_nonneg (x - roundEnergy x)
  have hs : (x - roundEnergy x)^2 ≤ 1 := by
    have hh := mul_nonneg (sub_nonneg.mpr h) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hn)
    nlinarith [sq_abs (x - roundEnergy x)]
  change (roundEnergy x)^2 ≤ 2*x^2+2
  nlinarith [sq_nonneg (2*x - roundEnergy x)]

theorem coupling_squared_cost_integrable {μ ν : Measure ℝ}
    {γ : Measure (ℝ × ℝ)} (hγ : γ ∈ couplings μ ν)
    (hμ : Integrable (fun x : ℝ => x^2) μ)
    (hν : Integrable (fun x : ℝ => x^2) ν) :
    Integrable (fun p : ℝ × ℝ => (p.1-p.2)^2) γ := by
  have hp : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
  have hq : MeasurePreserving Prod.snd γ ν := ⟨measurable_snd, hγ.2⟩
  have hx : Integrable (fun p : ℝ × ℝ => p.1^2) γ :=
    hp.integrable_comp_of_integrable hμ
  have hy : Integrable (fun p : ℝ × ℝ => p.2^2) γ :=
    hq.integrable_comp_of_integrable hν
  apply ((hx.const_mul 2).add (hy.const_mul 2)).mono'
    (by fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (p.1-p.2)^2 ≤ 2*p.1^2+2*p.2^2
  nlinarith [sq_nonneg (p.1+p.2)]

theorem round_squared_displacement_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℝ => (x - roundEnergy x)^2) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hm := measurable_id.sub measurable_roundEnergy
    exact (hm.pow_const 2).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := round_displacement_le_one x
    have hn := abs_nonneg (x-roundEnergy x)
    have hh := mul_nonneg (sub_nonneg.mpr h) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hn)
    nlinarith [sq_abs (x-roundEnergy x)]

theorem coupling_squared_nearest_ae (μ : Measure ℝ) (γ : Measure (ℝ × ℝ))
    (hγ : γ ∈ couplings μ (Measure.map roundEnergy μ)) :
    ∀ᵐ p ∂γ, (p.1-roundEnergy p.1)^2 ≤ (p.1-p.2)^2 := by
  filter_upwards [coupling_nearest_ae μ γ hγ] with p hp
  have hh := mul_nonneg (sub_nonneg.mpr hp)
    (add_nonneg (abs_nonneg (p.1-p.2)) (abs_nonneg (p.1-roundEnergy p.1)))
  nlinarith [sq_abs (p.1-p.2), sq_abs (p.1-roundEnergy p.1)]

theorem graph_squared_cost_eq_ae (μ : Measure ℝ) :
    ∀ᵐ p ∂(Measure.map (fun x : ℝ => (x, roundEnergy x)) μ),
      (p.1-p.2)^2 = (p.1-roundEnergy p.1)^2 := by
  filter_upwards [graph_cost_eq_ae μ] with p hp
  have h := congrArg (fun t : ℝ => t^2) hp
  simpa only [sq_abs] using h

/-- W₂² is the actual optimal quadratic primal cost; this requires
only the natural finite-second-moment hypothesis on the source. -/
theorem round_wasserstein2_squared (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x^2) μ) :
    wasserstein2Squared μ (Measure.map roundEnergy μ) =
      ∫ x, (x-roundEnergy x)^2 ∂μ := by
  exact Manuscript15.MagneticGibbs.GraphPrimalBridge.graph_primal_infimum
    μ roundEnergy measurable_roundEnergy (fun p => (p.1-p.2)^2)
    (fun x => (x-roundEnergy x)^2) (round_squared_displacement_integrable μ)
    (fun γ hγ => coupling_squared_cost_integrable hγ hμ (rounded_second_moment μ hμ))
    (coupling_squared_nearest_ae μ) (graph_squared_cost_eq_ae μ)

theorem round_wasserstein2_squared_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x^2) μ) :
    0 ≤ wasserstein2Squared μ (Measure.map roundEnergy μ) ∧
    wasserstein2Squared μ (Measure.map roundEnergy μ) ≤ 1 := by
  rw [round_wasserstein2_squared μ hμ]
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hle : ∀ᵐ x ∂μ, (x-roundEnergy x)^2 ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := round_displacement_le_one x
    have hh := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg (x-roundEnergy x)))
    nlinarith [sq_abs (x-roundEnergy x)]
  have h := integral_mono_ae (round_squared_displacement_integrable μ)
    (integrable_const (1:ℝ)) hle
  simpa using h

end Manuscript15.MagneticGibbs.Rounding

#print axioms Manuscript15.MagneticGibbs.Rounding.rounded_second_moment
#print axioms Manuscript15.MagneticGibbs.Rounding.coupling_squared_cost_integrable
#print axioms Manuscript15.MagneticGibbs.Rounding.round_squared_displacement_integrable
#print axioms Manuscript15.MagneticGibbs.Rounding.coupling_squared_nearest_ae
#print axioms Manuscript15.MagneticGibbs.Rounding.graph_squared_cost_eq_ae
#print axioms Manuscript15.MagneticGibbs.Rounding.round_wasserstein2_squared
#print axioms Manuscript15.MagneticGibbs.Rounding.round_wasserstein2_squared_bounds
