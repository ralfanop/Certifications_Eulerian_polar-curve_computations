import Mathlib

/-!
# Manuscript 15 (13 November revision): Sections 2.1 and 2.6

Independent real-algebraic cores of:
* Proposition 'Speed and curvature realisations' (Section 2.1);
* Proposition 'Laplace transform, Cayley matrix and unitime' (Section 2.6).

These theorems concern actual trigonometric expressions and the real rational
Cayley coordinates. They do NOT assert the analytic Laplace transform, Segal
physical interpretation, complex matrix identity, or the complete manifold
curvature theorem. Those are separate formalization obligations.
-/

open Real

noncomputable section

namespace Manuscript15.Section21And26

/-- Double-angle identity used to compute the speed of the actual cycloid. -/
theorem one_sub_cos_eq_two_sin_half_sq (t : ℝ) :
    1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  have ht : 2 * (t / 2) = t := by ring
  rw [ht] at hc
  nlinarith

/-- Squared Euclidean speed of the genuine cycloid parametrization. -/
theorem cycloid_speed_squared (a t : ℝ) :
    (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
      (2 * a * Real.sin (t / 2)) ^ 2 := by
  have hc := one_sub_cos_eq_two_sin_half_sq t
  have hs := Real.sin_sq_add_cos_sq t
  calc
    (a * (1 - Real.cos t)) ^ 2 + (a * Real.sin t) ^ 2 =
        a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
    _ = a ^ 2 * (2 * (1 - Real.cos t)) := by
      congr 1
      nlinarith
    _ = a ^ 2 * (4 * Real.sin (t / 2) ^ 2) := by rw [hc]; ring
    _ = (2 * a * Real.sin (t / 2)) ^ 2 := by ring

/-- Positive-speed formula for the actual cycloid on any half-angle
interval where the sine is nonnegative. -/
theorem cycloid_speed (a t : ℝ) (ha : 0 ≤ a)
    (hs : 0 ≤ Real.sin (t / 2)) :
    Real.sqrt ((a * (1 - Real.cos t)) ^ 2 +
      (a * Real.sin t) ^ 2) = 2 * a * Real.sin (t / 2) := by
  rw [cycloid_speed_squared, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- Determinant of the first and second cycloid derivative vectors. -/
theorem cycloid_derivative_determinant (a t : ℝ) :
    (a * (1 - Real.cos t)) * (a * Real.cos t) -
      (a * Real.sin t) * (a * Real.sin t) =
        -(a ^ 2) * (1 - Real.cos t) := by
  have hs := Real.sin_sq_add_cos_sq t
  have ht : (1 - Real.cos t) * Real.cos t - Real.sin t ^ 2 =
      -(1 - Real.cos t) := by nlinarith
  calc
    (a * (1 - Real.cos t)) * (a * Real.cos t) -
        (a * Real.sin t) * (a * Real.sin t) =
          a ^ 2 * ((1 - Real.cos t) * Real.cos t - Real.sin t ^ 2) := by ring
    _ = -(a ^ 2) * (1 - Real.cos t) := by rw [ht]; ring

/-- Absolute determinant, avoiding an implicit sign convention. -/
theorem cycloid_abs_derivative_determinant (a t : ℝ) :
    |(a * (1 - Real.cos t)) * (a * Real.cos t) -
      (a * Real.sin t) * (a * Real.sin t)| =
        a ^ 2 * (1 - Real.cos t) := by
  rw [cycloid_derivative_determinant]
  have h : 0 ≤ a ^ 2 * (1 - Real.cos t) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [Real.cos_le_one t])
  have he : -(a ^ 2) * (1 - Real.cos t) =
      -(a ^ 2 * (1 - Real.cos t)) := by ring
  rw [he, abs_neg, abs_of_nonneg h]

/-- The curvature quotient from the actual cycloid derivative jets.
Positivity isolates the nonsingular part of the cycloidal arc. -/
theorem cycloid_curvature_quotient (a t : ℝ)
    (ha : 0 < a) (hs : 0 < Real.sin (t / 2)) :
    |(a * (1 - Real.cos t)) * (a * Real.cos t) -
      (a * Real.sin t) * (a * Real.sin t)| /
      (2 * a * Real.sin (t / 2)) ^ 3 =
        1 / (4 * a * Real.sin (t / 2)) := by
  rw [cycloid_abs_derivative_determinant,
    one_sub_cos_eq_two_sin_half_sq]
  have han : a ≠ 0 := ne_of_gt ha
  have hsn : Real.sin (t / 2) ≠ 0 := ne_of_gt hs
  field_simp [han, hsn]
  <;> ring

/-- Rational real coordinate of the scalar Cayley transform at real q. -/
def cayleyReal (q : ℝ) : ℝ := (q ^ 2 - 1) / (q ^ 2 + 1)

/-- Rational imaginary coordinate of the scalar Cayley transform at real q. -/
def cayleyImag (q : ℝ) : ℝ := -(2 * q) / (q ^ 2 + 1)

/-- The rational Cayley coordinates lie exactly on the unit circle. -/
theorem cayley_coordinates_unit_circle (q : ℝ) :
    cayleyReal q ^ 2 + cayleyImag q ^ 2 = 1 := by
  have hn : q ^ 2 + 1 ≠ 0 := by positivity
  unfold cayleyReal cayleyImag
  field_simp [hn]
  <;> ring

/-- Exact apex Cayley real component for q = 1/2. -/
theorem cayley_real_at_half : cayleyReal (1 / 2) = -(3 / 5) := by
  norm_num [cayleyReal]

/-- Exact apex Cayley imaginary component for q = 1/2. -/
theorem cayley_imag_at_half : cayleyImag (1 / 2) = -(4 / 5) := by
  norm_num [cayleyImag]

/-- The Section 2.6 conformal factor at q = 1/2. -/
theorem conformal_factor_at_half :
    (1 : ℝ) / (1 + (1 / 2 : ℝ) ^ 2) = 4 / 5 := by
  norm_num


/-- First derivative of the actual cycloid's X coordinate. -/
theorem cycloid_X_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun x : ℝ => a * (x - Real.sin x))
      (a * (1 - Real.cos t)) t := by
  convert ((hasDerivAt_id' t).sub (hasDerivAt_sin t)).const_mul a using 1
  <;> ring

/-- First derivative of the actual cycloid's Y coordinate. -/
theorem cycloid_Y_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun x : ℝ => a * (1 - Real.cos x))
      (a * Real.sin t) t := by
  convert ((hasDerivAt_cos t).const_sub 1).const_mul a using 1
  <;> ring

/-- Derivative of the first component of the velocity. -/
theorem cycloid_velocity_X_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun x : ℝ => a * (1 - Real.cos x))
      (a * Real.sin t) t := cycloid_Y_hasDerivAt a t

/-- Derivative of the second component of the velocity. -/
theorem cycloid_velocity_Y_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun x : ℝ => a * Real.sin x)
      (a * Real.cos t) t := by
  convert (hasDerivAt_sin t).const_mul a using 1
  <;> ring

#print axioms Manuscript15.Section21And26.cycloid_X_hasDerivAt
#print axioms Manuscript15.Section21And26.cycloid_Y_hasDerivAt
#print axioms Manuscript15.Section21And26.cycloid_velocity_X_hasDerivAt
#print axioms Manuscript15.Section21And26.cycloid_velocity_Y_hasDerivAt

#print axioms Manuscript15.Section21And26.one_sub_cos_eq_two_sin_half_sq
#print axioms Manuscript15.Section21And26.cycloid_speed_squared
#print axioms Manuscript15.Section21And26.cycloid_speed
#print axioms Manuscript15.Section21And26.cycloid_derivative_determinant
#print axioms Manuscript15.Section21And26.cycloid_abs_derivative_determinant
#print axioms Manuscript15.Section21And26.cycloid_curvature_quotient
#print axioms Manuscript15.Section21And26.cayley_coordinates_unit_circle
#print axioms Manuscript15.Section21And26.cayley_real_at_half
#print axioms Manuscript15.Section21And26.cayley_imag_at_half
#print axioms Manuscript15.Section21And26.conformal_factor_at_half

end Manuscript15.Section21And26
