import Manuscript15.Section27CouplingIntegral

/-!
# Manuscript 15 §2.7 — simultaneous Fourier-coordinate transport

A two-coordinate consequence of the independently certified measure-level
cosine and sine inequalities. This is an L1-coordinate estimate for an
arbitrary coupling, not the Wasserstein infimum or a reconstruction theorem.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

/-- The two real Fourier coordinates obey a joint L1 coupling estimate. -/
theorem integral_fourier_two_coordinate_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ℝ) (s : ℝ)
    (hcx : Integrable (fun ω => Real.cos (s * x ω)) μ)
    (hcy : Integrable (fun ω => Real.cos (s * y ω)) μ)
    (hsx : Integrable (fun ω => Real.sin (s * x ω)) μ)
    (hsy : Integrable (fun ω => Real.sin (s * y ω)) μ)
    (hcost : Integrable (fun ω => |s| * |x ω - y ω|) μ) :
    |(∫ ω, Real.cos (s * x ω) ∂μ) -
      (∫ ω, Real.cos (s * y ω) ∂μ)| +
    |(∫ ω, Real.sin (s * x ω) ∂μ) -
      (∫ ω, Real.sin (s * y ω) ∂μ)| ≤
      2 * ∫ ω, |s| * |x ω - y ω| ∂μ := by
  have hc := integral_cosine_phase_coupling μ x y s hcx hcy hcost
  have hs := integral_sine_phase_coupling μ x y s hsx hsy hcost
  calc
    _ ≤ (∫ ω, |s| * |x ω - y ω| ∂μ) +
        (∫ ω, |s| * |x ω - y ω| ∂μ) := add_le_add hc hs
    _ = 2 * ∫ ω, |s| * |x ω - y ω| ∂μ := by ring

#print axioms Manuscript15.Section27.integral_fourier_two_coordinate_coupling

end Manuscript15.Section27
