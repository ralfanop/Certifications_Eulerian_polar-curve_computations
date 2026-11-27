import Mathlib
import EulerianCert.CassiniFeffermanTangent20261124

noncomputable section
namespace Manuscript17.CassiniPolynomialLift

open EulerianCert.CassiniFeffermanTangent20261124

/-! Cyclohedral.tex, thm:cassini-hemisphere-metric,
eq:m17-hemisphere-inverse, eq:m17-round-metric,
eq:m17-hyperbolic-metric, eq:m17-metric-conformal-factor.
Coordinates are (omega1,omega2,nu). All tangent directions, both hemispheres
and poles, not merely altitude/longitude coordinates. -/

def sphereDot (x y : Fin 3 → ℝ) : ℝ := x 0*y 0+x 1*y 1+x 2*y 2
def t (x : Fin 3 → ℝ) : ℝ := x 2/(2-x 2^2)
def rhoSq (x : Fin 3 → ℝ) : ℝ := (t x)^2*(1+x 0^2+x 1^2)
def lift (x : Fin 3 → ℝ) : V := ![t x*x 0,t x*x 1,rhoSq x,1,t x,1]
def scaledLift (x : Fin 3 → ℝ) : V := ![t x*x 0,t x*x 1,t x*x 2,1,t x,1]
def tangent (x u : Fin 3 → ℝ) (dt : ℝ) : V :=
  ![dt*x 0+t x*u 0,dt*x 1+t x*u 1,dt*x 2+t x*u 2,0,dt,0]

theorem denominator_pos (x : Fin 3 → ℝ) (hx : sphereDot x x = 1) :
    0 < 2-x 2^2 := by
  unfold sphereDot at hx
  nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

theorem rho_identity (x : Fin 3 → ℝ) (hx : sphereDot x x = 1) :
    rhoSq x = t x*x 2 := by
  have hq := denominator_pos x hx
  unfold sphereDot at hx
  unfold rhoSq t
  field_simp [hq.ne']
  nlinarith

theorem lift_eq_scaled (x : Fin 3 → ℝ) (hx : sphereDot x x = 1) :
    lift x = scaledLift x := by
  funext i
  fin_cases i <;> simp [lift, scaledLift, rho_identity x hx]

theorem lift_null (x : Fin 3 → ℝ) (hx : sphereDot x x = 1) :
    B (lift x) (lift x) = 0 := by
  rw [lift_eq_scaled x hx]
  simp [B, scaledLift]
  unfold sphereDot at hx
  linear_combination (t x)^2*hx

theorem tangent_metric (x u v : Fin 3 → ℝ) (dt et : ℝ)
    (hx : sphereDot x x = 1) (hu : sphereDot x u = 0)
    (hv : sphereDot x v = 0) :
    B (tangent x u dt) (tangent x v et) = (t x)^2 * sphereDot u v := by
  simp [B, tangent, sphereDot] at *
  linear_combination dt*et*hx+et*t x*hu+dt*t x*hv

/-- Differentiating the scaled representative gives the actual lift tangent,
for a curve in the sphere; the derivative of its third coordinate is included. -/
theorem lift_derivative (c : ℝ → Fin 3 → ℝ) (s dt : ℝ) (u : Fin 3 → ℝ)
    (hc : ∀ i, HasDerivAt (fun z => c z i) (u i) s)
    (hSphere : ∀ z, sphereDot (c z) (c z) = 1)
    (ht : HasDerivAt (fun z => t (c z)) dt s) (i : Fin 6) :
    HasDerivAt (fun z => lift (c z) i) (tangent (c s) u dt i) s := by
  have he : (fun z => lift (c z) i) = (fun z => scaledLift (c z) i) :=
    funext fun z => congrFun (lift_eq_scaled (c z) (hSphere z)) i
  rw [he]
  fin_cases i
  · simpa [scaledLift,tangent,add_comm,Pi.mul_apply] using ht.mul (hc 0)
  · simpa [scaledLift,tangent,add_comm,Pi.mul_apply] using ht.mul (hc 1)
  · simpa [scaledLift,tangent,add_comm,Pi.mul_apply] using ht.mul (hc 2)
  · simpa [scaledLift,tangent] using hasDerivAt_const s (1:ℝ)
  · simpa [scaledLift,tangent] using ht
  · simpa [scaledLift,tangent] using hasDerivAt_const s (1:ℝ)

def hyperTangent (x u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-u 2/(x 2)^2, (u 0*x 2-x 0*u 2)/(x 2)^2,
    (u 1*x 2-x 1*u 2)/(x 2)^2]
def lorentzDot (u v : Fin 3 → ℝ) : ℝ := -u 0*v 0+u 1*v 1+u 2*v 2

theorem hyper_metric (x u v : Fin 3 → ℝ) (hx : sphereDot x x = 1)
    (hu : sphereDot x u = 0) (hv : sphereDot x v = 0) (hn : x 2 ≠ 0) :
    lorentzDot (hyperTangent x u) (hyperTangent x v) = sphereDot u v/(x 2)^2 := by
  simp [lorentzDot,hyperTangent,sphereDot] at *
  field_simp [hn]
  linear_combination u 2*v 2*hx - x 2*v 2*hu - x 2*u 2*hv

theorem conformal_ratio (x u v : Fin 3 → ℝ) (dt et : ℝ)
    (hx : sphereDot x x = 1) (hu : sphereDot x u = 0)
    (hv : sphereDot x v = 0) (hn : x 2 ≠ 0) :
    B (tangent x u dt) (tangent x v et) =
      (rhoSq x)^2 * lorentzDot (hyperTangent x u) (hyperTangent x v) := by
  rw [tangent_metric x u v dt et hx hu hv, hyper_metric x u v hx hu hv hn,
    rho_identity x hx]
  field_simp [hn]
  <;> ring

#print axioms denominator_pos
#print axioms rho_identity
#print axioms lift_eq_scaled
#print axioms lift_null
#print axioms tangent_metric
#print axioms lift_derivative
#print axioms hyper_metric
#print axioms conformal_ratio

end Manuscript17.CassiniPolynomialLift
