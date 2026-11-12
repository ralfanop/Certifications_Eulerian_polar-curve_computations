/-
Manuscript 15 — formal terminal derivative classification for M>=2.

This combines three independently kernel-checked prerequisites:
- the true Eulerian sinc at its roots and convolution endpoint
  positions (PR #191);
- derivative of the Eulerian sinc at nonzero roots (PR #204);
- the generic power-zero derivative vanishing lemma (PR #203).

We prove that every convolution of M>=2 centred uniforms has
terminal tangent velocity (a,0). The M=1 singular cycloid
is a separate boundary case. No contact-order theorem is claimed.
-/
import Manuscript15.ConvolutionEndpoints
import Manuscript15.EulerianRootDerivatives
import Manuscript15.TerminalPowerJet
import Mathlib

open Real
noncomputable section
namespace Manuscript15

/-- Local differentiability of the rescaled Eulerian kernel r_E(2t)
    at t=2π, reusing the exact FourierModes nonzero-root derivative. -/
theorem eulerianKernel_double_hasDerivAt_terminal :
    HasDerivAt (fun t : ℝ => eulerianKernel (2 * t))
      (EulerianCert.Corner.rE' (2 * (2 * Real.pi)) * 2)
      (2 * Real.pi) := by
  have hnonzero : (2 : ℝ) * (2 * Real.pi) ≠ 0 := by positivity
  have hroot := eulerian_kernel_hasDerivAt_nonzero hnonzero
  have hlinear :
      HasDerivAt (fun t : ℝ => 2 * t) 2 (2 * Real.pi) := by
    convert (hasDerivAt_id (2 * Real.pi)).const_mul (2 : ℝ) using 1
    · funext t
      simp [mul_comm]
    · ring
  simpa only [Function.comp_def] using hroot.comp (2 * Real.pi) hlinear

/-- True X coordinate derivative at the convolution terminal point.
    Multiplicity M>=2 kills the derivative of the vanishing kernel
    power, leaving exactly the scale a. -/
theorem convolution_endpoint_X_hasDerivAt
    (a : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    HasDerivAt (XConv a M) a (2 * Real.pi) := by
  have hloc : eulerianKernel (2 * (2 * Real.pi)) = 0 := by
    have hh : 2 * (2 * Real.pi) = 4 * Real.pi := by ring
    rw [hh]
    exact eulerianKernel_four_pi_zero
  have hh := hasDerivAt_power_reconstruction_X a (2 * Real.pi)
    (EulerianCert.Corner.rE' (2 * (2 * Real.pi)) * 2)
    M hM (fun t : ℝ => eulerianKernel (2 * t))
    hloc eulerianKernel_double_hasDerivAt_terminal
  exact hh

/-- True Y coordinate derivative at the convolution terminal point.
    This vanishes for every M>=1. -/
theorem convolution_endpoint_Y_hasDerivAt
    (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    HasDerivAt (YConv a M) 0 (2 * Real.pi) := by
  have hn : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hroot := eulerian_kernel_hasDerivAt_nonzero hn
  have hh := hasDerivAt_power_reconstruction_Y a (2 * Real.pi)
    (EulerianCert.Corner.rE' (2 * Real.pi))
    M hM eulerianKernel eulerianKernel_two_pi_zero hroot
  exact hh

/-- Derivative-value version: regular terminal X velocity equals a. -/
theorem convolution_endpoint_X_deriv
    (a : ℝ) (M : ℕ) (hM : 2 ≤ M) :
    deriv (XConv a M) (2 * Real.pi) = a :=
  (convolution_endpoint_X_hasDerivAt a M hM).deriv

/-- Derivative-value version: Y velocity equals zero. -/
theorem convolution_endpoint_Y_deriv
    (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    deriv (YConv a M) (2 * Real.pi) = 0 :=
  (convolution_endpoint_Y_hasDerivAt a M hM).deriv

#print axioms Manuscript15.eulerianKernel_double_hasDerivAt_terminal
#print axioms Manuscript15.convolution_endpoint_X_hasDerivAt
#print axioms Manuscript15.convolution_endpoint_Y_hasDerivAt
#print axioms Manuscript15.convolution_endpoint_X_deriv
#print axioms Manuscript15.convolution_endpoint_Y_deriv

end Manuscript15
