/-
Manuscript 15 — exact Eulerian zeros and convolution endpoint coordinates.

This certifies the zero identities and endpoint *positions*. The
terminal derivative classification (singular M=1 versus regular M≥2)
is a separate proof obligation and is not claimed here.
-/
import EulerianCert.FourierModes
import Mathlib

open Real
noncomputable section
namespace Manuscript15

abbrev eulerianKernel : ℝ → ℝ := EulerianCert.FourierModes.rE

/-- The reconstruction of M centred uniforms, first coordinate. -/
def XConv (a : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  a * t * (1 - (eulerianKernel (2 * t)) ^ M)

/-- The reconstruction of M centred uniforms, second coordinate. -/
def YConv (a : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  a * t ^ 2 / 2 * (eulerianKernel t) ^ (2 * M)

/-- r_E(2π)=0, the first positive zero of the exact sinc kernel. -/
theorem eulerianKernel_two_pi_zero : eulerianKernel (2 * Real.pi) = 0 := by
  have hn : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [EulerianCert.FourierModes.rE_of_ne_zero hn]
  have hh : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hh, Real.sin_pi]
  ring

/-- r_E(4π)=0, as required for X_M(2π). -/
theorem eulerianKernel_four_pi_zero : eulerianKernel (4 * Real.pi) = 0 := by
  have hn : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [EulerianCert.FourierModes.rE_of_ne_zero hn]
  have hh : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hh, Real.sin_two_pi]
  ring

/-- The first coordinate of every nonempty convolution ends at 2πa. -/
theorem convolution_endpoint_X (a : ℝ) (M : ℕ) (hM : 0 < M) :
    XConv a M (2 * Real.pi) = 2 * Real.pi * a := by
  unfold XConv
  have hs : 2 * (2 * Real.pi) = 4 * Real.pi := by ring
  rw [hs, eulerianKernel_four_pi_zero]
  simp [hM]
  ring

/-- The second coordinate of every nonempty convolution vanishes at 2π. -/
theorem convolution_endpoint_Y (a : ℝ) (M : ℕ) (hM : 0 < M) :
    YConv a M (2 * Real.pi) = 0 := by
  unfold YConv
  rw [eulerianKernel_two_pi_zero]
  have hp : 0 < 2 * M := by omega
  simp [hp]

/-- All convolution curves start at the origin, for any M including M=0. -/
theorem convolution_origin_X (a : ℝ) (M : ℕ) :
    XConv a M 0 = 0 := by simp [XConv]

theorem convolution_origin_Y (a : ℝ) (M : ℕ) :
    YConv a M 0 = 0 := by simp [YConv]

#print axioms Manuscript15.eulerianKernel_two_pi_zero
#print axioms Manuscript15.eulerianKernel_four_pi_zero
#print axioms Manuscript15.convolution_endpoint_X
#print axioms Manuscript15.convolution_endpoint_Y
#print axioms Manuscript15.convolution_origin_X
#print axioms Manuscript15.convolution_origin_Y

end Manuscript15
