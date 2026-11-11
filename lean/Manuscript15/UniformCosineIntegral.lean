/-
Manuscript 15 — exact real cosine characteristic integral of the
centred uniform law. This bridges the genuine inherited Eulerian sinc
kernel to the elementary interval integral from -1/2 to 1/2.

The equality is for the real cosine integral; full uniqueness of
probability measures via complex Fourier transforms remains separate.
-/
import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib

open Real MeasureTheory intervalIntegral
noncomputable section
namespace Manuscript15

/-- Scaled cosine integral, valid for every real parameter including 0. -/
theorem uniform_cosine_scaled (t : ℝ) :
    t * (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (t * x)) =
      2 * Real.sin (t / 2) := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.cos) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) t
  have hl : t * (-1 / 2 : ℝ) = -(t / 2) := by ring
  have hr : t * (1 / 2 : ℝ) = t / 2 := by ring
  rw [hl, hr, intervalIntegral.integral_cos, Real.sin_neg] at h
  linarith

/-- The characteristic cosine transform of Unif[-1/2,1/2] is exactly
    the Eulerian sinc used throughout Manuscript 15. -/
theorem uniform_cosine_eq_eulerian (t : ℝ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (t * x)) =
      EulerianCert.FourierModes.rE t := by
  by_cases ht : t = 0
  · subst t
    simp [EulerianCert.FourierModes.rE_zero]
    norm_num
  · rw [EulerianCert.FourierModes.rE_of_ne_zero ht]
    have h := uniform_cosine_scaled t
    have hmul :
        t * (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (t * x)) =
          t * (2 * Real.sin (t / 2) / t) := by
      calc
        _ = 2 * Real.sin (t / 2) := h
        _ = t * (2 * Real.sin (t / 2) / t) := by
          field_simp [ht]
          ring
    exact mul_left_cancel₀ ht hmul

/-- The sine transform of the symmetric centred interval vanishes. -/
theorem uniform_sine_integral_zero (t : ℝ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.sin (t * x)) = 0 := by
  by_cases ht : t = 0
  · subst t
    simp
  · have h := intervalIntegral.mul_integral_comp_mul_left
        (f := Real.sin) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) t
    have hl : t * (-1 / 2 : ℝ) = -(t / 2) := by ring
    have hr : t * (1 / 2 : ℝ) = t / 2 := by ring
    rw [hl, hr, intervalIntegral.integral_sin, Real.cos_neg, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left ht

#print axioms Manuscript15.uniform_cosine_scaled
#print axioms Manuscript15.uniform_cosine_eq_eulerian
#print axioms Manuscript15.uniform_sine_integral_zero

end Manuscript15
