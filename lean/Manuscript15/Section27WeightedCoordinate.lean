import Manuscript15.Section27TwoCoordinate

/-!
# Manuscript 15 §2.7 — weighted Fourier coordinate transport

For any nonnegative real coordinate weights, the weighted L1 discrepancy
of the real and imaginary Fourier coordinates is bounded by the corresponding
weighted transport majorant. No Wasserstein infimum or uniqueness is asserted.
-/

open MeasureTheory

noncomputable section

namespace Manuscript15.Section27

theorem integral_fourier_weighted_coordinate_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → ℝ) (s a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcx : Integrable (fun ω => Real.cos (s * x ω)) μ)
    (hcy : Integrable (fun ω => Real.cos (s * y ω)) μ)
    (hsx : Integrable (fun ω => Real.sin (s * x ω)) μ)
    (hsy : Integrable (fun ω => Real.sin (s * y ω)) μ)
    (hcost : Integrable (fun ω => |s| * |x ω - y ω|) μ) :
    a * |(∫ ω, Real.cos (s * x ω) ∂μ) -
      (∫ ω, Real.cos (s * y ω) ∂μ)| +
    b * |(∫ ω, Real.sin (s * x ω) ∂μ) -
      (∫ ω, Real.sin (s * y ω) ∂μ)| ≤
      (a + b) * ∫ ω, |s| * |x ω - y ω| ∂μ := by
  have hc := integral_cosine_phase_coupling μ x y s hcx hcy hcost
  have hs := integral_sine_phase_coupling μ x y s hsx hsy hcost
  have hac := mul_le_mul_of_nonneg_left hc ha
  have hbs := mul_le_mul_of_nonneg_left hs hb
  calc
    _ ≤ a * (∫ ω, |s| * |x ω - y ω| ∂μ) +
        b * (∫ ω, |s| * |x ω - y ω| ∂μ) := add_le_add hac hbs
    _ = (a + b) * ∫ ω, |s| * |x ω - y ω| ∂μ := by ring

#print axioms Manuscript15.Section27.integral_fourier_weighted_coordinate_coupling

end Manuscript15.Section27
