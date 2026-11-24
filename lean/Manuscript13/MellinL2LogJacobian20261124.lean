import Mathlib

/-! M13, Theorem 4.14: logarithmic measure and actual L² composition.
The first theorem is the one-dimensional Lebesgue change of variables
with the explicit density 1/u. The L² map uses the pushforward measure
and is a genuine complex-linear isometry. The measure equality and surjectivity are also targeted below. Fourier
Plancherel transport and multiplication-operator norm remain separate. -/

open MeasureTheory Set
open scoped ENNReal
namespace Manuscript13.MellinL2LogJacobian20261124
noncomputable section

theorem log_image_positive : Real.log '' Ioi (0 : ℝ) = univ := by
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    exact ⟨Real.exp x, Real.exp_pos x, Real.log_exp x⟩

theorem log_injOn_positive : InjOn Real.log (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have h := congrArg Real.exp hxy
  simpa [Real.exp_log hx, Real.exp_log hy] using h

theorem log_jacobian (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt Real.log u⁻¹ (Ioi (0 : ℝ)) u :=
  (Real.hasDerivAt_log (ne_of_gt hu)).hasDerivWithinAt

theorem logarithmic_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, g x) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u⁻¹ * g (Real.log u) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    measurableSet_Ioi log_jacobian log_injOn_positive g
  rw [log_image_positive, Measure.restrict_univ] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hu))]

theorem logarithmic_energy (f : ℝ → ℂ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (‖f (Real.exp x)‖ ^ 2)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u⁻¹ *
        ENNReal.ofReal (‖f u‖ ^ 2) := by
  rw [logarithmic_lintegral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.exp_log hu]

def expMeasure : Measure ℝ := Measure.map Real.exp volume

theorem exp_measurePreserving :
    MeasurePreserving Real.exp volume expMeasure :=
  ⟨Real.continuous_exp.measurable, rfl⟩

def logL2 : Lp ℂ 2 expMeasure →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ Real.exp exp_measurePreserving

theorem logL2_norm (f : Lp ℂ 2 expMeasure) : ‖logL2 f‖ = ‖f‖ :=
  logL2.norm_map f

theorem logL2_ae (f : Lp ℂ 2 expMeasure) :
    (fun x : ℝ => logL2 f x) =ᵐ[volume] (fun x => f (Real.exp x)) := by
  change (fun x : ℝ => (Lp.compMeasurePreserving Real.exp exp_measurePreserving f) x) =ᵐ[volume] _
  exact Lp.coeFn_compMeasurePreserving f exp_measurePreserving

theorem exp_measure_positive : expMeasure (Ioi (0 : ℝ))ᶜ = 0 := by
  rw [expMeasure, Measure.map_apply Real.continuous_exp.measurable measurableSet_Ioi.compl]
  have h : Real.exp ⁻¹' (Ioi (0 : ℝ))ᶜ = ∅ := by
    ext x
    simp [Real.exp_pos x]
  rw [h, measure_empty]

def logarithmicDensity : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
    (fun u => ENNReal.ofReal u⁻¹)

theorem exp_measure_eq_density : expMeasure = logarithmicDensity := by
  ext s hs
  let g : ℝ → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hs
  calc
    expMeasure s = ∫⁻ u, g u ∂expMeasure := by
      simp [g, lintegral_indicator hs]
    _ = ∫⁻ x : ℝ, g (Real.exp x) := by
      exact lintegral_map hg Real.continuous_exp.measurable
    _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u⁻¹ * g u := by
      rw [logarithmic_lintegral]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.exp_log hu]
    _ = ∫⁻ u, g u ∂logarithmicDensity := by
      unfold logarithmicDensity
      rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
      rfl
    _ = logarithmicDensity s := by simp [g, lintegral_indicator hs]

theorem log_measurePreserving :
    MeasurePreserving Real.log expMeasure volume := by
  refine ⟨Real.measurable_log, ?_⟩
  rw [expMeasure, Measure.map_map Real.measurable_log Real.continuous_exp.measurable]
  have h : Real.log ∘ Real.exp = id := by
    funext x
    exact Real.log_exp x
  rw [h, Measure.map_id]

def expL2 : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 expMeasure :=
  Lp.compMeasurePreservingₗᵢ ℂ Real.log log_measurePreserving

theorem logL2_surjective : Function.Surjective logL2 := by
  intro f
  refine ⟨expL2 f, ?_⟩
  change Lp.compMeasurePreserving Real.exp exp_measurePreserving
    (Lp.compMeasurePreserving Real.log log_measurePreserving f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f log_measurePreserving exp_measurePreserving]
  have h : Real.log ∘ Real.exp = id := by
    funext x
    exact Real.log_exp x
  simp [h]

def logUnitary : Lp ℂ 2 expMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective logL2 logL2_surjective

theorem logUnitary_norm (f : Lp ℂ 2 expMeasure) : ‖logUnitary f‖ = ‖f‖ :=
  logUnitary.norm_map f

/-- Continuous functions on the spectral band cannot hide a larger
value at a null endpoint: any strict excess persists on an interval. -/
def bandMeasure : Measure ℝ := volume.restrict (Icc (-(1/2 : ℝ)) (1/2 : ℝ))

theorem band_interval_positive (a b : ℝ) (hab : a < b)
    (ha : -(1/2 : ℝ) ≤ a) (hb : b ≤ 1/2) :
    bandMeasure (Ioo a b) ≠ 0 := by
  unfold bandMeasure
  rw [Measure.restrict_apply measurableSet_Ioo]
  have h : Ioo a b ∩ Icc (-(1/2 : ℝ)) (1/2 : ℝ) = Ioo a b := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨le_trans ha hx.1.le, le_trans hx.2.le hb⟩
  rw [h, Real.volume_Ioo]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))

theorem ae_band_bound_is_pointwise (m : ℝ → ℝ) (hm : Continuous m)
    (C : ℝ) (hC : ∀ᵐ x ∂bandMeasure, m x ≤ C)
    (x : ℝ) (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ)) : m x ≤ C := by
  by_contra! hbad
  have ho : IsOpen {z : ℝ | C < m z} := isOpen_lt continuous_const hm
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho x hbad
  let ε : ℝ := min (δ/2) (1/2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεhalf : ε ≤ 1/2 := min_le_right _ _
  have hz : bandMeasure {z : ℝ | ¬ m z ≤ C} = 0 := ae_iff.mp hC
  by_cases hside : x ≤ 0
  · have hsub : Ioo x (x+ε) ⊆ {z : ℝ | ¬ m z ≤ C} := by
      intro z hz'
      apply not_le.mpr
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hz'.1)]
      linarith [hz'.2]
    have hn := band_interval_positive x (x+ε) (by linarith) hx.1 (by linarith)
    exact hn (le_antisymm (hz ▸ measure_mono hsub) bot_le)
  · have hsub : Ioo (x-ε) x ⊆ {z : ℝ | ¬ m z ≤ C} := by
      intro z hz'
      apply not_le.mpr
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hz'.2)]
      linarith [hz'.1]
    have hn := band_interval_positive (x-ε) x (by linarith) (by linarith) hx.2
    exact hn (le_antisymm (hz ▸ measure_mono hsub) bot_le)

theorem sharp_essential_bound (m : ℝ → ℝ) (hm : Continuous m) (C : ℝ)
    (hupper : ∀ x ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ), m x ≤ C)
    (hattain : ∃ x ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ), m x = C) :
    IsLeast {b : ℝ | ∀ᵐ x ∂bandMeasure, m x ≤ b} C := by
  constructor
  · change ∀ᵐ x ∂bandMeasure, m x ≤ C
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with x hx
    exact hupper x hx
  · intro b hb
    obtain ⟨x, hx, heq⟩ := hattain
    rw [← heq]
    exact ae_band_bound_is_pointwise m hm b hb x hx

/-- The actual Rindler multiplier; no assumption that its endpoint
maximum is also essential is made. Pointwise bounds/attainment are
the already certified #568 declarations and are explicit arguments
here to keep the module independently compilable. -/
theorem rindler_essential_bound (n : ℤ)
    (hupper : ∀ x ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ),
      Real.exp (-(2*Real.pi*(n : ℝ)*x)) ≤ Real.exp (Real.pi*|(n : ℝ)|))
    (hattain : ∃ x ∈ Icc (-(1/2 : ℝ)) (1/2 : ℝ),
      Real.exp (-(2*Real.pi*(n : ℝ)*x)) = Real.exp (Real.pi*|(n : ℝ)|)) :
    IsLeast {b : ℝ | ∀ᵐ x ∂bandMeasure,
      Real.exp (-(2*Real.pi*(n : ℝ)*x)) ≤ b}
      (Real.exp (Real.pi*|(n : ℝ)|)) := by
  apply sharp_essential_bound _ (by fun_prop) _ hupper hattain

end
end Manuscript13.MellinL2LogJacobian20261124

#print axioms Manuscript13.MellinL2LogJacobian20261124.log_image_positive
#print axioms Manuscript13.MellinL2LogJacobian20261124.log_injOn_positive
#print axioms Manuscript13.MellinL2LogJacobian20261124.log_jacobian
#print axioms Manuscript13.MellinL2LogJacobian20261124.logarithmic_lintegral
#print axioms Manuscript13.MellinL2LogJacobian20261124.logarithmic_energy
#print axioms Manuscript13.MellinL2LogJacobian20261124.exp_measurePreserving
#print axioms Manuscript13.MellinL2LogJacobian20261124.logL2
#print axioms Manuscript13.MellinL2LogJacobian20261124.logL2_norm
#print axioms Manuscript13.MellinL2LogJacobian20261124.logL2_ae
#print axioms Manuscript13.MellinL2LogJacobian20261124.exp_measure_positive

#print axioms Manuscript13.MellinL2LogJacobian20261124.exp_measure_eq_density
#print axioms Manuscript13.MellinL2LogJacobian20261124.log_measurePreserving
#print axioms Manuscript13.MellinL2LogJacobian20261124.expL2
#print axioms Manuscript13.MellinL2LogJacobian20261124.logL2_surjective
#print axioms Manuscript13.MellinL2LogJacobian20261124.logUnitary
#print axioms Manuscript13.MellinL2LogJacobian20261124.logUnitary_norm

#print axioms Manuscript13.MellinL2LogJacobian20261124.band_interval_positive
#print axioms Manuscript13.MellinL2LogJacobian20261124.ae_band_bound_is_pointwise
#print axioms Manuscript13.MellinL2LogJacobian20261124.sharp_essential_bound
#print axioms Manuscript13.MellinL2LogJacobian20261124.rindler_essential_bound
