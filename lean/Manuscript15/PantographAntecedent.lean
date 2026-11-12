/-
Manuscript 15 — exact conversion of its cycloidal kinematic equation
to the classical nonlinear pantograph equation (Ozturk–Gulsu antecedent).

This proves the differentiation and substitution identities, and both
logical implications at a point given the derivative of f at 2t.
No Cauchy uniqueness or characteristic-function uniqueness is asserted.
-/
import Mathlib

noncomputable section
namespace Manuscript15

/-- The rescaled characteristic function y(t)=t f(2t). -/
def pantographTransform (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * f (2 * t)

/-- Exact algebraic equality of the nonlinear terms. -/
theorem pantograph_quadratic_identity (f : ℝ → ℝ) (t : ℝ) :
    2 * (pantographTransform f (t / 2)) ^ 2 =
      t ^ 2 / 2 * (f t) ^ 2 := by
  unfold pantographTransform
  have ht : 2 * (t / 2) = t := by ring
  rw [ht]
  ring

/-- Differentiation of y(t)=t f(2t) at points where f is differentiable. -/
theorem pantograph_hasDerivAt (f : ℝ → ℝ) (t d : ℝ)
    (hf : HasDerivAt f d (2 * t)) :
    HasDerivAt (pantographTransform f) (f (2 * t) + 2 * t * d) t := by
  have hlinear : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    convert (hasDerivAt_id t).const_mul (2 : ℝ) using 1
    · funext s
      simp [mul_comm]
    · ring
  have hcomp : HasDerivAt (fun s : ℝ => f (2 * s)) (d * 2) t :=
    hf.comp t hlinear
  have h := (hasDerivAt_id t).mul hcomp
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- The characteristic-function equation implies the earlier published
    nonlinear pantograph differential equation. -/
theorem pantograph_equation_of_kinematic (f : ℝ → ℝ) (t d : ℝ)
    (hf : HasDerivAt f d (2 * t))
    (hkin : 1 - f (2 * t) - 2 * t * d = t ^ 2 / 2 * (f t) ^ 2) :
    HasDerivAt (pantographTransform f)
      (1 - 2 * (pantographTransform f (t / 2)) ^ 2) t := by
  have hrewrite :
      f (2 * t) + 2 * t * d =
        1 - 2 * (pantographTransform f (t / 2)) ^ 2 := by
    rw [pantograph_quadratic_identity]
    linarith
  rw [← hrewrite]
  exact pantograph_hasDerivAt f t d hf

/-- Conversely, the pantograph differential equation recovers the
    exact scalar kinematic equation at the same point. -/
theorem kinematic_of_pantograph_equation (f : ℝ → ℝ) (t d : ℝ)
    (hf : HasDerivAt f d (2 * t))
    (hy : HasDerivAt (pantographTransform f)
      (1 - 2 * (pantographTransform f (t / 2)) ^ 2) t) :
    1 - f (2 * t) - 2 * t * d = t ^ 2 / 2 * (f t) ^ 2 := by
  have hunique := (pantograph_hasDerivAt f t d hf).unique hy
  rw [pantograph_quadratic_identity] at hunique
  linarith

/-- The sine function solves y'=1-2y(t/2)^2 pointwise. -/
theorem sine_pantograph_hasDerivAt (t : ℝ) :
    HasDerivAt Real.sin (1 - 2 * (Real.sin (t / 2)) ^ 2) t := by
  have hc := Real.cos_two_mul (t / 2)
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  have ht : 2 * (t / 2) = t := by ring
  rw [ht] at hc
  convert Real.hasDerivAt_sin t using 1 <;> nlinarith

#print axioms Manuscript15.pantograph_quadratic_identity
#print axioms Manuscript15.pantograph_hasDerivAt
#print axioms Manuscript15.pantograph_equation_of_kinematic
#print axioms Manuscript15.kinematic_of_pantograph_equation
#print axioms Manuscript15.sine_pantograph_hasDerivAt

end Manuscript15
