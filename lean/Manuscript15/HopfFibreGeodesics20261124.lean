import Manuscript15.HopfSubmersionDifferential20261124
import Mathlib

/-!
# M15: actual Hopf-fibre great-circle ODE in ambient real coordinates

The proof of prop:hopf-basic-laplace in the source M15 of 24 Nov 2026
uses the fact that Hopf fibres are great circles, and hence have zero
mean curvature. This module verifies the actual Hopf-circle flow,
its time derivatives, and the ambient geodesic ODE.

The full intrinsic Levi-Civita geodesic equation, minimal-fibre
submersion Laplacian intertwining, and Fefferman wave-operator conjugacy
are separate obligations; this file does not claim them.
-/

namespace Manuscript15.HopfFibreGeodesics20261124

open Manuscript15.HopfDifferential20261124

/-- The actual negative Hopf-circle action e^(-it) on ℂ² ≅ ℝ⁴. -/
noncomputable def orbit (q : HopfQ) (t : ℝ) : HopfQ :=
  phaseRotate (Real.cos t) (-Real.sin t) q

/-- Preservation of the actual ambient squared norm. -/
theorem orbit_normSq4 (q : HopfQ) (t : ℝ) :
    normSq4 (orbit q t) = normSq4 q := by
  dsimp [orbit]
  rw [normSq4_phaseRotate]
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- The actual Hopf map is constant on the complete circle orbit. -/
theorem orbit_hopfMap (q : HopfQ) (t : ℝ) :
    hopfMap (orbit q t) = hopfMap q := by
  exact hopfMap_negative_circle_orbit q t

/-- The real Hopf-fibre velocity has norm one on the unit sphere. -/
theorem orbit_vertical_unit_speed (q : HopfQ) (hq : normSq4 q = 1)
    (t : ℝ) :
    dot4 (verticalGenerator (orbit q t)) (verticalGenerator (orbit q t)) = 1 := by
  rw [vertical_length_sq, orbit_normSq4, hq]

/-- First coordinate: actual time derivative of the Hopf orbit. -/
theorem orbit11_hasDerivAt (q : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (orbit q s).1.1) ((orbit q t).1.2) t := by
  have h := ((Real.hasDerivAt_cos t).const_mul q.1.1).add
    ((Real.hasDerivAt_sin t).const_mul q.1.2)
  convert h using 1 <;> try { funext s } <;> dsimp [orbit, phaseRotate] <;> ring

/-- Second coordinate: actual time derivative of the Hopf orbit. -/
theorem orbit12_hasDerivAt (q : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (orbit q s).1.2) (-(orbit q t).1.1) t := by
  have h := ((Real.hasDerivAt_sin t).const_mul (-q.1.1)).add
    ((Real.hasDerivAt_cos t).const_mul q.1.2)
  convert h using 1 <;> try { funext s } <;> dsimp [orbit, phaseRotate] <;> ring

/-- Third coordinate: actual time derivative of the Hopf orbit. -/
theorem orbit21_hasDerivAt (q : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (orbit q s).2.1) ((orbit q t).2.2) t := by
  have h := ((Real.hasDerivAt_cos t).const_mul q.2.1).add
    ((Real.hasDerivAt_sin t).const_mul q.2.2)
  convert h using 1 <;> try { funext s } <;> dsimp [orbit, phaseRotate] <;> ring

/-- Fourth coordinate: actual time derivative of the Hopf orbit. -/
theorem orbit22_hasDerivAt (q : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (orbit q s).2.2) (-(orbit q t).2.1) t := by
  have h := ((Real.hasDerivAt_sin t).const_mul (-q.2.1)).add
    ((Real.hasDerivAt_cos t).const_mul q.2.2)
  convert h using 1 <;> try { funext s } <;> dsimp [orbit, phaseRotate] <;> ring

/-- The first coordinate satisfies the genuine second-order ODE γ''=-γ. -/
theorem orbit11_second_deriv (q : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).1.1) s) t =
      -(orbit q t).1.1 := by
  have hfun :
      (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).1.1) s) =
        (fun s : ℝ => (orbit q s).1.2) := by
    funext s
    exact (orbit11_hasDerivAt q s).deriv
  rw [hfun]
  exact (orbit12_hasDerivAt q t).deriv

/-- The second coordinate satisfies the genuine ODE γ''=-γ. -/
theorem orbit12_second_deriv (q : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).1.2) s) t =
      -(orbit q t).1.2 := by
  have hfun :
      (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).1.2) s) =
        (fun s : ℝ => -(orbit q s).1.1) := by
    funext s
    exact (orbit12_hasDerivAt q s).deriv
  rw [hfun]
  exact ((orbit11_hasDerivAt q t).neg).deriv

/-- The third coordinate satisfies the genuine ODE γ''=-γ. -/
theorem orbit21_second_deriv (q : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).2.1) s) t =
      -(orbit q t).2.1 := by
  have hfun :
      (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).2.1) s) =
        (fun s : ℝ => (orbit q s).2.2) := by
    funext s
    exact (orbit21_hasDerivAt q s).deriv
  rw [hfun]
  exact (orbit22_hasDerivAt q t).deriv

/-- The fourth coordinate satisfies the genuine ODE γ''=-γ. -/
theorem orbit22_second_deriv (q : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).2.2) s) t =
      -(orbit q t).2.2 := by
  have hfun :
      (fun s : ℝ => deriv (fun r : ℝ => (orbit q r).2.2) s) =
        (fun s : ℝ => -(orbit q s).2.1) := by
    funext s
    exact (orbit22_hasDerivAt q s).deriv
  rw [hfun]
  exact ((orbit21_hasDerivAt q t).neg).deriv

/-- Unit-time flow starts at the original point. -/
theorem orbit_zero (q : HopfQ) : orbit q 0 = q := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [orbit, phaseRotate]

/-- Half a fibre period implements the actual antipodal map. -/
theorem orbit_pi_antipodal (q : HopfQ) : orbit q Real.pi = -q := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [orbit, phaseRotate]

#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit_normSq4
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit_hopfMap
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit_vertical_unit_speed
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit11_hasDerivAt
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit12_hasDerivAt
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit21_hasDerivAt
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit22_hasDerivAt
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit11_second_deriv
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit12_second_deriv
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit21_second_deriv
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit22_second_deriv
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit_zero
#print axioms Manuscript15.HopfFibreGeodesics20261124.orbit_pi_antipodal

end Manuscript15.HopfFibreGeodesics20261124
