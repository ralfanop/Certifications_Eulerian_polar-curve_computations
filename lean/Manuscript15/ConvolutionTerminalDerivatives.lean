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
import Manuscript15.CycloidalReconstruction
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

/-! ### Complete M=1 versus M≥2 velocity classification -/

/-- For exactly one centred uniform summand the first reconstructed
    coordinate is the original Eulerian cycloid. Its terminal derivative
    vanishes, unlike the nonzero a derivative for every M>=2. -/
theorem convolution_endpoint_X_one_hasDerivAt (a : ℝ) :
    HasDerivAt (XConv a 1) 0 (2 * Real.pi) := by
  have hX : XConv a 1 = X a eulerianSinc := by
    funext t
    simp [XConv, X, eulerianKernel, eulerianSinc]
  rw [hX]
  have hy : Y a eulerianSinc (2 * Real.pi) = 0 := by
    rw [eulerian_Y_eq_cycloid, Real.cos_two_pi]
    ring
  simpa only [hy] using eulerian_kinematic a (2 * Real.pi)

/-- All positive convolution orders are classified at the endpoint:
    M=1 has X derivative 0, M>=2 has X derivative a. -/
theorem convolution_terminal_X_deriv_classification
    (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    deriv (XConv a M) (2 * Real.pi) =
      if M = 1 then 0 else a := by
  by_cases hOne : M = 1
  · subst M
    simpa using (convolution_endpoint_X_one_hasDerivAt a).deriv
  · have hMore : 2 ≤ M := by omega
    simpa [hOne] using convolution_endpoint_X_deriv a M hMore

/-- Exact endpoint velocity for every positive convolution order.
    The point is stationary iff M=1 or the scale a is zero. -/
theorem convolution_terminal_velocity_classification
    (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    (deriv (XConv a M) (2 * Real.pi),
       deriv (YConv a M) (2 * Real.pi)) =
      (if M = 1 then 0 else a, 0) := by
  rw [convolution_terminal_X_deriv_classification a M hM,
    convolution_endpoint_Y_deriv a M hM]

/-- The one-summand cycloid has exactly zero terminal velocity. -/
theorem convolution_terminal_one_stationary (a : ℝ) :
    (deriv (XConv a 1) (2 * Real.pi),
      deriv (YConv a 1) (2 * Real.pi)) = (0, 0) := by
  simpa using convolution_terminal_velocity_classification a 1 (by omega)

/-- Every M>=2 is regular at the terminal point if a≠0. -/
theorem convolution_terminal_higher_regular
    (a : ℝ) (ha : a ≠ 0) (M : ℕ) (hM : 2 ≤ M) :
    (deriv (XConv a M) (2 * Real.pi),
      deriv (YConv a M) (2 * Real.pi)) ≠ (0, 0) := by
  have hv := convolution_terminal_velocity_classification a M (by omega)
  have hm : M ≠ 1 := by omega
  rw [if_neg hm] at hv
  rw [hv]
  simp [ha]

#print axioms Manuscript15.convolution_endpoint_X_one_hasDerivAt
#print axioms Manuscript15.convolution_terminal_X_deriv_classification
#print axioms Manuscript15.convolution_terminal_velocity_classification
#print axioms Manuscript15.convolution_terminal_one_stationary
#print axioms Manuscript15.convolution_terminal_higher_regular

#print axioms Manuscript15.eulerianKernel_double_hasDerivAt_terminal
#print axioms Manuscript15.convolution_endpoint_X_hasDerivAt
#print axioms Manuscript15.convolution_endpoint_Y_hasDerivAt
#print axioms Manuscript15.convolution_endpoint_X_deriv
#print axioms Manuscript15.convolution_endpoint_Y_deriv

end Manuscript15
