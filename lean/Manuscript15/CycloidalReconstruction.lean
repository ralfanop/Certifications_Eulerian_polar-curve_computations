/-
Manuscript 15 — initial Lean 4 formalization, 10 November 2026.
Scope: exact real cycloidal reconstruction from the pre-existing Eulerian sinc.
This module is deliberately independent of any proposed gravitational interpretation.
It must be compiled and axiom-audited by CI before being counted as certified.
-/
import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

noncomputable section

namespace Manuscript15

/-- First coordinate of the cycloidal reconstruction from a real function. -/
def X (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t * (1 - f (2 * t))

/-- Second coordinate of the cycloidal reconstruction from a real function. -/
def Y (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t ^ 2 / 2 * (f t) ^ 2

/-- The existing, kernel-checked Eulerian sinc, from Manuscript 11. -/
abbrev eulerianSinc : ℝ → ℝ := EulerianCert.FourierModes.rE

/-- The Eulerian sinc reconstructs the cycloid's first coordinate. -/
theorem eulerian_X_eq_cycloid (a t : ℝ) :
    X a eulerianSinc t = a * (t - Real.sin t) := by
  by_cases ht : t = 0
  · subst t
    simp [X]
  · have h2 : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
    unfold X eulerianSinc
    rw [EulerianCert.FourierModes.rE_of_ne_zero h2]
    have hhalf : (2 * t) / 2 = t := by ring
    rw [hhalf]
    have hcancel : t * (2 * Real.sin t / (2 * t)) = Real.sin t := by
      field_simp [ht]
      <;> ring
    calc
      a * t * (1 - 2 * Real.sin t / (2 * t)) =
          a * (t - t * (2 * Real.sin t / (2 * t))) := by ring
      _ = a * (t - Real.sin t) := by rw [hcancel]

/-- The Eulerian sinc reconstructs the cycloid's second coordinate. -/
theorem eulerian_Y_eq_cycloid (a t : ℝ) :
    Y a eulerianSinc t = a * (1 - Real.cos t) := by
  by_cases ht : t = 0
  · subst t
    simp [Y]
  · have hsinc : eulerianSinc t = 2 * Real.sin (t / 2) / t :=
      EulerianCert.FourierModes.rE_of_ne_zero ht
    have hcancel :
        t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2 =
          2 * Real.sin (t / 2) ^ 2 := by
      field_simp [ht]
      <;> ring
    have hangle : 2 * Real.sin (t / 2) ^ 2 = 1 - Real.cos t := by
      have hc := Real.cos_two_mul (t / 2)
      have hsc := Real.sin_sq_add_cos_sq (t / 2)
      have htwice : 2 * (t / 2) = t := by ring
      rw [htwice] at hc
      nlinarith
    unfold Y
    rw [hsinc]
    calc
      a * t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2 =
          a * (t ^ 2 / 2 * (2 * Real.sin (t / 2) / t) ^ 2) := by ring
      _ = a * (2 * Real.sin (t / 2) ^ 2) := by rw [hcancel]
      _ = a * (1 - Real.cos t) := by rw [hangle]

/-- Kinematic identity of the reconstructed cycloid (Manuscript 15, Eq. X'=Y).
This does not yet certify uniqueness among probability measures. -/
theorem eulerian_kinematic (a t : ℝ) :
    HasDerivAt (X a eulerianSinc) (Y a eulerianSinc t) t := by
  have hfun : X a eulerianSinc = fun x => a * (x - Real.sin x) := by
    funext x
    exact eulerian_X_eq_cycloid a x
  rw [hfun, eulerian_Y_eq_cycloid]
  convert ((hasDerivAt_id' t).sub (hasDerivAt_sin t)).const_mul a using 1 <;> ring

/-- Algebraic leading-order cusp constant. The analytic limit is a later target. -/
theorem cusp_leading_coefficient (a v t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (2 * a * v * t ^ 3) ^ 2 / ((a / 2 * t ^ 2) ^ 3) =
      32 * v ^ 2 / a := by
  field_simp [ha, ht]
  <;> ring

/-- The distinguished coordinate of the standard cycloid. -/
theorem eulerian_Y_pi (a : ℝ) :
    Y a eulerianSinc Real.pi = 2 * a := by
  rw [eulerian_Y_eq_cycloid, Real.cos_pi]
  ring

#print axioms Manuscript15.eulerian_X_eq_cycloid
#print axioms Manuscript15.eulerian_Y_eq_cycloid
#print axioms Manuscript15.eulerian_kinematic
#print axioms Manuscript15.cusp_leading_coefficient
#print axioms Manuscript15.eulerian_Y_pi

end Manuscript15
