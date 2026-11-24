import Manuscript15.HopfFibreGeodesics20261124
import Mathlib

/-!
# M15 Fefferman scalar conjugacy: the actual Hopf real-cover map

This is the concrete real-coordinate specialization, on the universal
cover ℝ × ℂ², of eq:hopf-fefferman-phi and
eq:hopf-fefferman-equivariance in M15 24 Nov 2026.

M16 FeffermanDeckAlgebra20261123 already proves a GROUP-THEORETIC
equivariance. Here the actual trigonometric Hopf-circle map is
constructed, shown invertible, shown to preserve the round metric,
and shown to intertwine the actual deck transformations. Basic
scalar pullbacks and their true first time derivatives are preserved.

The quotient by 2πℤ, Fefferman Lorentzian metric identification,
wave operator on smooth manifold functions and spectral domains
are not claimed by this file; they are separate obligations.
-/

namespace Manuscript15.FeffermanRealCover20261124

open Manuscript15.HopfDifferential20261124
open Manuscript15.HopfFibreGeodesics20261124

/-- Group property of the *actual* negative Hopf-circle flow. -/
theorem orbit_add (q : HopfQ) (s t : ℝ) :
    orbit (orbit q s) t = orbit q (s + t) := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [orbit, phaseRotate, Real.cos_add, Real.sin_add] <;> ring <;> simp

/-- The real flow is linear and commutes with the antipodal map. -/
theorem orbit_neg (q : HopfQ) (t : ℝ) :
    orbit (-q) t = -(orbit q t) := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [orbit, phaseRotate] <;> ring <;> simp

/-- Diagonal antipodality and a half-period time shift cancel
inside the actual Hopf-circle flow, on its real universal cover. -/
theorem orbit_antipodal_shift (q : HopfQ) (t : ℝ) :
    orbit (-q) (t + Real.pi) = orbit q t := by
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [orbit, phaseRotate, Real.cos_add_pi, Real.sin_add_pi] <;> ring

/-- The explicit scalar-coordinate Fefferman chart Φ(t,q). -/
noncomputable def phi (p : ℝ × HopfQ) : ℝ × HopfQ :=
  (p.1, orbit p.2 p.1)

/-- The true inverse chart (t,q) ↦ (t,e^(it)q). -/
noncomputable def phiInv (p : ℝ × HopfQ) : ℝ × HopfQ :=
  (p.1, orbit p.2 (-p.1))

/-- The explicit map has a two-sided left inverse on ℝ×ℂ². -/
theorem phi_left_inverse (p : ℝ × HopfQ) : phiInv (phi p) = p := by
  rcases p with ⟨t, q⟩
  simp only [phiInv, phi]
  rw [orbit_add]
  simpa using orbit_zero q

/-- The explicit map has a two-sided right inverse on ℝ×ℂ². -/
theorem phi_right_inverse (p : ℝ × HopfQ) : phi (phiInv p) = p := by
  rcases p with ⟨t, q⟩
  simp only [phiInv, phi]
  rw [orbit_add]
  simpa using orbit_zero q

/-- On the real cover, diagonal involution deck map from M15. -/
noncomputable def iotaCover (p : ℝ × HopfQ) : ℝ × HopfQ :=
  (p.1 + Real.pi, -p.2)

/-- On the real cover, time-only deck map from M15. -/
noncomputable def deckACover (p : ℝ × HopfQ) : ℝ × HopfQ :=
  (p.1 + Real.pi, p.2)

/-- Concrete global Fefferman deck equivariance on the universal cover,
before the quotient to S¹. It proves Φ∘ι=A∘Φ for the actual real
trigonometric Hopf map, not just an unspecified group action. -/
theorem phi_deck_equivariance (p : ℝ × HopfQ) :
    phi (iotaCover p) = deckACover (phi p) := by
  rcases p with ⟨t, q⟩
  simp only [phi, iotaCover, deckACover]
  rw [orbit_antipodal_shift]

/-- Real U(1) Hopf-circle action is an ambient Euclidean isometry
for *any* pair of vectors, not just for their lengths. -/
theorem orbit_dot_isometry (v w : HopfQ) (t : ℝ) :
    dot4 (orbit v t) (orbit w t) = dot4 v w := by
  rcases v with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases w with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  have htrig := Real.cos_sq_add_sin_sq t
  calc
    dot4 (orbit ((a, b), (c, d)) t) (orbit ((e, f), (g, h)) t) =
      (Real.cos t ^ 2 + Real.sin t ^ 2) *
        dot4 ((a, b), (c, d)) ((e, f), (g, h)) := by
        dsimp [dot4, orbit, phaseRotate]
        ring
    _ = dot4 ((a, b), (c, d)) ((e, f), (g, h)) := by
      rw [htrig]
      ring

/-- Every Hopf-basic scalar field is fixed by the ACTUAL
Fefferman chart P=Φ*, even when its external scalar factor a(t)
is arbitrary and not assumed smooth. -/
theorem basic_field_phi_invariant
    (a : ℝ → ℝ) (f : ((ℝ × ℝ) × ℝ) → ℝ) (p : ℝ × HopfQ) :
    a (phi p).1 * f (hopfMap (phi p).2) =
      a p.1 * f (hopfMap p.2) := by
  rcases p with ⟨t, q⟩
  dsimp [phi]
  rw [orbit_hopfMap]

/-- Actual time derivative of a Hopf-basic scalar pullback
along the Fefferman map. It equals da times the fixed spatial
basic factor; no fictitious wave-operator axiom is inserted. -/
theorem basic_field_time_derivative
    (a : ℝ → ℝ) (da : ℝ) (f : ((ℝ × ℝ) × ℝ) → ℝ)
    (q : HopfQ) (t : ℝ) (ha : HasDerivAt a da t) :
    HasDerivAt (fun s : ℝ => a s * f (hopfMap (orbit q s)))
      (da * f (hopfMap q)) t := by
  have hfun :
      (fun s : ℝ => a s * f (hopfMap (orbit q s))) =
      (fun s : ℝ => a s * f (hopfMap q)) := by
    funext s
    rw [orbit_hopfMap]
  rw [hfun]
  exact ha.mul_const (f (hopfMap q))

#print axioms Manuscript15.FeffermanRealCover20261124.orbit_add
#print axioms Manuscript15.FeffermanRealCover20261124.orbit_neg
#print axioms Manuscript15.FeffermanRealCover20261124.orbit_antipodal_shift
#print axioms Manuscript15.FeffermanRealCover20261124.phi_left_inverse
#print axioms Manuscript15.FeffermanRealCover20261124.phi_right_inverse
#print axioms Manuscript15.FeffermanRealCover20261124.phi_deck_equivariance
#print axioms Manuscript15.FeffermanRealCover20261124.orbit_dot_isometry
#print axioms Manuscript15.FeffermanRealCover20261124.basic_field_phi_invariant
#print axioms Manuscript15.FeffermanRealCover20261124.basic_field_time_derivative

end Manuscript15.FeffermanRealCover20261124
