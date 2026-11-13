import Mathlib

/-!
# Manuscript 15, November 13 revision — Section 2.7

The measure-theoretic transport step missing from the earlier *finite*
Kantorovich and Fourier transport modules (#285–#287).

Each theorem is for a general measurable space and an actual Bochner integral
against an arbitrary measure, under explicit integrability hypotheses.
The final Wasserstein-1 infimum/characteristic-function marginal transport
and the 2-coordinate reconstruction statement are not asserted in this file.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- A pointwise bound on the difference of two integrable real observables
gives a rigorous bound on the difference of their integrals. This is the
actual infinite-measure-space coupling step (not a finite-sum surrogate). -/
theorem integral_transport_of_pointwise_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g cost : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hcost : Integrable cost μ)
    (hbound : ∀ ω, |f ω - g ω| ≤ cost ω) :
    |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| ≤
      ∫ ω, cost ω ∂μ := by
  have hpoint : ∀ᵐ ω ∂μ, ‖f ω - g ω‖ ≤ cost ω :=
    Filter.Eventually.of_forall (by
      intro ω
      simpa only [Real.norm_eq_abs] using hbound ω)
  have hmain :
      ‖∫ ω, f ω - g ω ∂μ‖ ≤ ∫ ω, cost ω ∂μ :=
    MeasureTheory.norm_integral_le_of_norm_le
      (f := fun ω => f ω - g ω)
      (g := cost) hcost hpoint
  calc
    |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| =
        |∫ ω, f ω - g ω ∂μ| := by
          rw [integral_sub hf hg]
    _ = ‖∫ ω, f ω - g ω ∂μ‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ ω, cost ω ∂μ := hmain

/-- General Lipschitz test-function inequality on a genuine coupling
space, conditional only on the appropriate integrability hypotheses. -/
theorem integral_unit_lipschitz_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ℝ) (φ : ℝ → ℝ)
    (hx : Integrable (fun ω => φ (x ω)) μ)
    (hy : Integrable (fun ω => φ (y ω)) μ)
    (hcost : Integrable (fun ω => |x ω - y ω|) μ)
    (hLip : ∀ u v : ℝ, |φ u - φ v| ≤ |u - v|) :
    |(∫ ω, φ (x ω) ∂μ) - (∫ ω, φ (y ω) ∂μ)| ≤
      ∫ ω, |x ω - y ω| ∂μ := by
  apply integral_transport_of_pointwise_bound μ
    (fun ω => φ (x ω)) (fun ω => φ (y ω))
    (fun ω => |x ω - y ω|) hx hy hcost
  intro ω
  exact hLip (x ω) (y ω)

/-- Fourier cosine phase transport on an arbitrary coupling space.
The necessary integrability of the scaled transport cost is explicit. -/
theorem integral_cosine_phase_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ℝ) (s : ℝ)
    (hx : Integrable (fun ω => Real.cos (s * x ω)) μ)
    (hy : Integrable (fun ω => Real.cos (s * y ω)) μ)
    (hcost : Integrable (fun ω => |s| * |x ω - y ω|) μ) :
    |(∫ ω, Real.cos (s * x ω) ∂μ) -
      (∫ ω, Real.cos (s * y ω) ∂μ)| ≤
      ∫ ω, |s| * |x ω - y ω| ∂μ := by
  apply integral_transport_of_pointwise_bound μ
    (fun ω => Real.cos (s * x ω))
    (fun ω => Real.cos (s * y ω))
    (fun ω => |s| * |x ω - y ω|) hx hy hcost
  intro ω
  calc
    |Real.cos (s * x ω) - Real.cos (s * y ω)| ≤
        |s * x ω - s * y ω| := Real.abs_cos_sub_cos_le _ _
    _ = |s| * |x ω - y ω| := by rw [← mul_sub, abs_mul]

/-- Fourier sine phase transport on an arbitrary coupling space. -/
theorem integral_sine_phase_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ℝ) (s : ℝ)
    (hx : Integrable (fun ω => Real.sin (s * x ω)) μ)
    (hy : Integrable (fun ω => Real.sin (s * y ω)) μ)
    (hcost : Integrable (fun ω => |s| * |x ω - y ω|) μ) :
    |(∫ ω, Real.sin (s * x ω) ∂μ) -
      (∫ ω, Real.sin (s * y ω) ∂μ)| ≤
      ∫ ω, |s| * |x ω - y ω| ∂μ := by
  apply integral_transport_of_pointwise_bound μ
    (fun ω => Real.sin (s * x ω))
    (fun ω => Real.sin (s * y ω))
    (fun ω => |s| * |x ω - y ω|) hx hy hcost
  intro ω
  calc
    |Real.sin (s * x ω) - Real.sin (s * y ω)| ≤
        |s * x ω - s * y ω| := Real.abs_sin_sub_sin_le _ _
    _ = |s| * |x ω - y ω| := by rw [← mul_sub, abs_mul]

#print axioms Manuscript15.Section27.integral_transport_of_pointwise_bound
#print axioms Manuscript15.Section27.integral_unit_lipschitz_coupling
#print axioms Manuscript15.Section27.integral_cosine_phase_coupling
#print axioms Manuscript15.Section27.integral_sine_phase_coupling

end Manuscript15.Section27
