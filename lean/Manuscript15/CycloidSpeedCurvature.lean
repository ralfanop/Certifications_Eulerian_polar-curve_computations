/-
Manuscript 15, Proposition "Speed and curvature realisations".

Formalises the exact trigonometric speed identity and the signed
curvature determinant numerator of the actual cycloidal parametrisation,
using the previously established X'(t)=a(1-cos t), Y'(t)=a sin t.

The full curvature quotient and radius require additional nonzero
velocity/positivity and algebraic denominator steps, tracked separately.
-/
import Mathlib

open Real
noncomputable section
namespace Manuscript15

/-- Double-angle reduction, with no excluded parameters. -/
theorem cycloid_one_sub_cos (t : ℝ) :
    1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  have ht : 2 * (t / 2) = t := by ring
  rw [ht] at hc
  nlinarith

/-- Exact square of the speed of the standard cycloid,
    including its cusps, for every real scale a and parameter t. -/
theorem cycloid_speed_squared (a t : ℝ) :
    (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
      4 * a ^ 2 * Real.sin (t / 2) ^ 2 := by
  calc
    _ = a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
    _ = a ^ 2 * (2 * (1 - Real.cos t)) := by
      have hs := Real.sin_sq_add_cos_sq t
      congr 1
      nlinarith
    _ = 4 * a ^ 2 * Real.sin (t / 2) ^ 2 := by
      rw [cycloid_one_sub_cos]
      ring

/-- The determinant numerator of planar curvature is exactly
    a^2(cos t -1), so the unsigned curvature numerator is its absolute. -/
theorem cycloid_curvature_determinant (a t : ℝ) :
    (a * (1 - Real.cos t)) * (a * Real.cos t) -
      (a * Real.sin t) * (a * Real.sin t) =
        a ^ 2 * (Real.cos t - 1) := by
  calc
    _ = a ^ 2 * ((1 - Real.cos t) * Real.cos t -
      Real.sin t ^ 2) := by ring
    _ = a ^ 2 * (Real.cos t - 1) := by
      have hs := Real.sin_sq_add_cos_sq t
      congr 1
      nlinarith

/-- On the regular positive arc, the exact speed is
    2a*sin(t/2); this is a true square-root identity. -/
theorem cycloid_speed (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (htop : t < 2 * Real.pi) :
    Real.sqrt ((a * (1 - Real.cos t)) ^ 2 +
      (a * Real.sin t) ^ 2) = 2 * a * Real.sin (t / 2) := by
  have hsin : 0 < Real.sin (t / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  rw [cycloid_speed_squared]
  have hsq :
      4 * a ^ 2 * Real.sin (t / 2) ^ 2 =
        (2 * a * Real.sin (t / 2)) ^ 2 := by ring
  rw [hsq]
  exact Real.sqrt_sq (le_of_lt (mul_pos (mul_pos (by norm_num) ha) hsin))

/-! ### Full unsigned curvature and its radius on the regular arc -/

/-- The ordinary unsigned curvature of the parametrised cycloid. -/
def cycloidCurvature (a t : ℝ) : ℝ :=
    |(a * (1 - Real.cos t)) * (a * Real.cos t) -
       (a * Real.sin t) * (a * Real.sin t)| /
      (Real.sqrt ((a * (1 - Real.cos t)) ^ 2 +
        (a * Real.sin t) ^ 2)) ^ 3

/-- The exact curvature 1/(4a sin(t/2)), with the regular-arc
    hypotheses explicitly excluding zero speed at t=0 and 2π. -/
theorem cycloid_curvature_exact (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (htop : t < 2 * Real.pi) :
    cycloidCurvature a t = 1 / (4 * a * Real.sin (t / 2)) := by
  have hsin : 0 < Real.sin (t / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hnum :
      a ^ 2 * (Real.cos t - 1) =
       -(2 * a ^ 2 * Real.sin (t / 2) ^ 2) := by
    have h := cycloid_one_sub_cos t
    nlinarith
  have hnonneg : 0 ≤ 2 * a ^ 2 * Real.sin (t / 2) ^ 2 := by positivity
  have hden : 2 * a * Real.sin (t / 2) ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hs0 : Real.sin (t / 2) ≠ 0 := ne_of_gt hsin
  unfold cycloidCurvature
  rw [cycloid_curvature_determinant, cycloid_speed a t ha ht htop, hnum,
      abs_neg, abs_of_nonneg hnonneg]
  field_simp [ha0, hs0, hden]
  <;> ring

/-- The exact osculating radius, reciprocal to the unsigned curvature,
    is 4a sin(t/2) on the entire regular positive cycloidal arc. -/
theorem cycloid_curvature_radius (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (htop : t < 2 * Real.pi) :
    (cycloidCurvature a t)⁻¹ = 4 * a * Real.sin (t / 2) := by
  rw [cycloid_curvature_exact a t ha ht htop]
  have hs : Real.sin (t / 2) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0, hs]
  <;> ring

#print axioms Manuscript15.cycloid_curvature_exact
#print axioms Manuscript15.cycloid_curvature_radius

#print axioms Manuscript15.cycloid_one_sub_cos
#print axioms Manuscript15.cycloid_speed_squared
#print axioms Manuscript15.cycloid_curvature_determinant
#print axioms Manuscript15.cycloid_speed

end Manuscript15
