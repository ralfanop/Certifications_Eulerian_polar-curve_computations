import Mathlib

/-! M13, Theorem 4.14: logarithmic measure and actual L² composition.
The first theorem is the one-dimensional Lebesgue change of variables
with the explicit density 1/u. The L² map uses the pushforward measure
and is a genuine complex-linear isometry. Identification of the
pushforward with the density, surjectivity, Fourier Plancherel transport
and multiplication-operator norm are distinct proof obligations. -/

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
