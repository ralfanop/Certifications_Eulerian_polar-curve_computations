import Mathlib
import Manuscript17.CassiniPolynomialLift20261127

noncomputable section
namespace Manuscript17.CassiniGlobalImage

open Manuscript17.CassiniPolynomialLift

/-! Global image of the actual northern sphere parametrization in its
three affine coordinates. The equator maps to one point. This is an
algebraic/topological precursor, not an identification of path metrics. -/

def northern (x : Fin 3 → ℝ) : Prop := sphereDot x x = 1 ∧ 0 ≤ x 2
def imagePoint (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => t x * x i
def surface (y : Fin 3 → ℝ) : Prop :=
  y 2 = 2*(y 0)^2 + 2*(y 1)^2 + (y 2)^2

def radial (y : Fin 3 → ℝ) : ℝ := Real.sqrt (sphereDot y y)
def inversePoint (y : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => y i / radial y

theorem image_on_surface (x : Fin 3 → ℝ) (hx : northern x) :
    surface (imagePoint x) := by
  have h := rho_identity x hx.1
  unfold rhoSq at h
  have hs := hx.1
  unfold sphereDot at hs
  unfold surface imagePoint
  linear_combination -h - (t x)^2*hs

theorem equator_collapse (x : Fin 3 → ℝ) (hx : northern x) :
    imagePoint x = 0 ↔ x 2 = 0 := by
  constructor
  · intro h
    have hz := congrFun h (2 : Fin 3)
    change t x*x 2 = 0 at hz
    rcases mul_eq_zero.mp hz with ht | h2
    · exact (div_eq_zero_iff.mp ht).resolve_right (denominator_pos x hx.1).ne'
    · exact h2
  · intro h
    have ht : t x = 0 := by simp [t,h]
    funext i
    simp [imagePoint,ht]

theorem radial_pos (y : Fin 3 → ℝ) (hy : y ≠ 0) : 0 < radial y := by
  apply Real.sqrt_pos.2
  unfold sphereDot
  by_contra! h
  have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  have h2 : y 2 = 0 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  apply hy
  funext i
  fin_cases i <;> assumption

theorem radial_sq (y : Fin 3 → ℝ) : radial y^2 = sphereDot y y := by
  apply Real.sq_sqrt
  unfold sphereDot
  nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]

theorem inverse_northern (y : Fin 3 → ℝ) (hy : surface y) (hn : y ≠ 0) :
    northern (inversePoint y) := by
  have hp := radial_pos y hn
  have hs := radial_sq y
  unfold sphereDot at hs
  constructor
  · unfold inversePoint sphereDot
    field_simp [hp.ne']
    nlinarith
  · unfold inversePoint
    apply div_nonneg _ hp.le
    unfold surface at hy
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]

theorem inverse_scale (y : Fin 3 → ℝ) (hy : surface y) (hn : y ≠ 0) :
    t (inversePoint y) = radial y := by
  have hp := radial_pos y hn
  have hs := radial_sq y
  have hq := denominator_pos (inversePoint y) (inverse_northern y hy hn).1
  unfold sphereDot at hs
  unfold surface at hy
  have he : 2*radial y^2 - (y 2)^2 = y 2 := by linarith
  unfold t inversePoint at hq ⊢
  apply (div_eq_iff hq.ne').2
  field_simp [hp.ne']
  <;> linear_combination (radial y)*(-he)

theorem image_inverse (y : Fin 3 → ℝ) (hy : surface y) (hn : y ≠ 0) :
    imagePoint (inversePoint y) = y := by
  funext i
  unfold imagePoint inversePoint
  rw [show t (fun j => y j / radial y) = radial y from inverse_scale y hy hn]
  field_simp [(radial_pos y hn).ne']

theorem radial_image (x : Fin 3 → ℝ) (hx : northern x) :
    radial (imagePoint x) = t x := by
  have ht : 0 ≤ t x := div_nonneg hx.2 (denominator_pos x hx.1).le
  unfold radial sphereDot imagePoint
  have hs := hx.1
  unfold sphereDot at hs
  rw [show t x*x 0*(t x*x 0)+t x*x 1*(t x*x 1)+t x*x 2*(t x*x 2) = (t x)^2 by
    linear_combination (t x)^2*hs]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

theorem inverse_image (x : Fin 3 → ℝ) (hx : northern x) (hp : 0 < x 2) :
    inversePoint (imagePoint x) = x := by
  have ht : 0 < t x := div_pos hp (denominator_pos x hx.1)
  funext i
  unfold inversePoint
  rw [radial_image x hx]
  unfold imagePoint
  field_simp [ht.ne']

#print axioms image_on_surface
#print axioms equator_collapse
#print axioms radial_pos
#print axioms radial_sq
#print axioms inverse_northern
#print axioms inverse_scale
#print axioms image_inverse
#print axioms radial_image
#print axioms inverse_image
end Manuscript17.CassiniGlobalImage
