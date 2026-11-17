import Manuscript15.ConvolutionTerminalDerivatives

/-!
M15 terminal contact: genuine all-order leading limit, not a finite Taylor
test. For M≥2 the regular X coordinate converts parametric contact to
graph contact. The analytic local inverse and the full Lagrange–Bürmann
remainder/coefficients are still separate obligations.
-/

open Filter Topology
noncomputable section
namespace Manuscript15.TerminalContact

open Manuscript15

/-- Leading transverse contact in the original parameter, for every M. -/
theorem parametric_contact (a : ℝ) (M : ℕ) :
    Tendsto (fun t : ℝ => YConv a M t / (t - 2 * Real.pi) ^ (2 * M))
      (𝓝[≠] (2 * Real.pi))
      (𝓝 (a * (2 * Real.pi) ^ 2 / 2 * (-1 / (2 * Real.pi)) ^ (2 * M))) := by
  have hk : Tendsto
      (fun t : ℝ => eulerianKernel t / (t - 2 * Real.pi))
      (𝓝[≠] (2 * Real.pi)) (𝓝 (-1 / (2 * Real.pi))) := by
    simpa only [slope_fun_def_field, eulerianKernel_two_pi_zero, sub_zero]
      using eulerian_kernel_hasDerivAt_two_pi.tendsto_slope
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] (2 * Real.pi))
      (𝓝 (2 * Real.pi)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun _ : ℝ => a) (𝓝[≠] (2 * Real.pi)) (𝓝 a) :=
    tendsto_const_nhds
  have h := ((ha.mul (ht.pow 2)).div_const 2).mul (hk.pow (2 * M))
  apply h.congr'
  filter_upwards with t
  change a * t ^ 2 / 2 * (eulerianKernel t / (t - 2 * Real.pi)) ^ (2 * M) =
    YConv a M t / (t - 2 * Real.pi) ^ (2 * M)
  rw [div_pow, ← mul_div_assoc, YConv]

/-- Leading contact with the horizontal tangent, in the actual X-coordinate
of the regular terminal curve. This is an all-M limit, no unproved Taylor
expansion or hypothesized local inverse. -/
theorem graph_contact (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M) :
    Tendsto (fun t : ℝ =>
      YConv a M t / (XConv a M t - XConv a M (2 * Real.pi)) ^ (2 * M))
      (𝓝[≠] (2 * Real.pi))
      (𝓝 ((a * (2 * Real.pi) ^ 2 / 2 * (-1 / (2 * Real.pi)) ^ (2 * M)) /
        a ^ (2 * M))) := by
  have hx : Tendsto
      (fun t : ℝ => (XConv a M t - XConv a M (2 * Real.pi)) /
        (t - 2 * Real.pi))
      (𝓝[≠] (2 * Real.pi)) (𝓝 a) := by
    simpa only [slope_fun_def_field] using
      (convolution_endpoint_X_hasDerivAt a M hM).tendsto_slope
  have h := (parametric_contact a M).div (hx.pow (2 * M)) (pow_ne_zero _ ha)
  apply h.congr'
  have hn : ∀ᶠ t : ℝ in 𝓝[≠] (2 * Real.pi), t ≠ 2 * Real.pi :=
    self_mem_nhdsWithin
  filter_upwards [hn] with t ht
  change (YConv a M t / (t - 2 * Real.pi) ^ (2 * M)) /
    ((XConv a M t - XConv a M (2 * Real.pi)) / (t - 2 * Real.pi)) ^ (2 * M) =
    YConv a M t / (XConv a M t - XConv a M (2 * Real.pi)) ^ (2 * M)
  rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero _ (sub_ne_zero.mpr ht))]

/-- The leading coefficient is nonzero at every nondegenerate scale.
Thus the all-order transverse limit does not certify only an upper bound. -/
theorem graph_contact_coefficient_ne_zero (a : ℝ) (ha : a ≠ 0) (M : ℕ) :
    (a * (2 * Real.pi) ^ 2 / 2 * (-1 / (2 * Real.pi)) ^ (2 * M)) /
      a ^ (2 * M) ≠ 0 := by
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  exact div_ne_zero (mul_ne_zero
    (div_ne_zero (mul_ne_zero ha (pow_ne_zero _ hp)) (by norm_num))
    (pow_ne_zero _ (div_ne_zero (by norm_num) hp))) (pow_ne_zero _ ha)

end Manuscript15.TerminalContact

#print axioms Manuscript15.TerminalContact.parametric_contact
#print axioms Manuscript15.TerminalContact.graph_contact
#print axioms Manuscript15.TerminalContact.graph_contact_coefficient_ne_zero
