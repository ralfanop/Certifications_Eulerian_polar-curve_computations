/-
Manuscript 15 — local differentiability of the genuine Eulerian
characteristic kernel r_E(t) = sinc(t/2) at its nonzero spectral roots.

Bridge from the exact FourierModes kernel (used in Manuscript 15)
to the previously kernel-certified nonzero quotient derivative in
EulerianCert.Corner (Manuscript 11).
-/
import EulerianCert.FourierModes
import EulerianCert.Corner
import Mathlib

open Real Filter Topology
noncomputable section
namespace Manuscript15

/-- The two inherited definitions agree on every nonzero parameter. -/
theorem eulerian_kernel_nonzero_eq_corner {t : ℝ} (ht : t ≠ 0) :
    EulerianCert.FourierModes.rE t = EulerianCert.Corner.rE t := by
  rw [EulerianCert.FourierModes.rE_of_ne_zero ht]
  rfl

/-- Exact local derivative of the *same* Eulerian sinc used in the
    manuscript; this removes the apparent 0/0 singularity only away
    from t=0, where the quotient representation is valid. -/
theorem eulerian_kernel_hasDerivAt_nonzero {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt EulerianCert.FourierModes.rE
      (EulerianCert.Corner.rE' t) t := by
  have hevent :
      EulerianCert.FourierModes.rE =ᶠ[𝓝 t] EulerianCert.Corner.rE := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    exact eulerian_kernel_nonzero_eq_corner hu
  exact (EulerianCert.Corner.hasDerivAt_rE ht).congr_of_eventuallyEq hevent

/-- The first positive zero r_E(2π) has derivative -1/(2π). -/
theorem eulerian_kernel_derivative_two_pi :
    EulerianCert.Corner.rE' (2 * Real.pi) =
      -1 / (2 * Real.pi) := by
  unfold EulerianCert.Corner.rE'
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf, Real.cos_pi, Real.sin_pi]
  ring

/-- The next zero r_E(4π) has derivative +1/(4π). -/
theorem eulerian_kernel_derivative_four_pi :
    EulerianCert.Corner.rE' (4 * Real.pi) =
      1 / (4 * Real.pi) := by
  unfold EulerianCert.Corner.rE'
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hhalf, Real.cos_two_pi, Real.sin_two_pi]
  ring

theorem eulerian_kernel_hasDerivAt_two_pi :
    HasDerivAt EulerianCert.FourierModes.rE
      (-1 / (2 * Real.pi)) (2 * Real.pi) := by
  have hn : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  convert eulerian_kernel_hasDerivAt_nonzero hn using 1
  exact eulerian_kernel_derivative_two_pi.symm

theorem eulerian_kernel_hasDerivAt_four_pi :
    HasDerivAt EulerianCert.FourierModes.rE
      (1 / (4 * Real.pi)) (4 * Real.pi) := by
  have hn : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  convert eulerian_kernel_hasDerivAt_nonzero hn using 1
  exact eulerian_kernel_derivative_four_pi.symm

#print axioms Manuscript15.eulerian_kernel_nonzero_eq_corner
#print axioms Manuscript15.eulerian_kernel_hasDerivAt_nonzero
#print axioms Manuscript15.eulerian_kernel_derivative_two_pi
#print axioms Manuscript15.eulerian_kernel_derivative_four_pi
#print axioms Manuscript15.eulerian_kernel_hasDerivAt_two_pi
#print axioms Manuscript15.eulerian_kernel_hasDerivAt_four_pi

end Manuscript15
