import Manuscript15.HopfSubmersionDifferential20261124
import Mathlib

/-!
# M15 — the actual horizontal differential metric of the Hopf map

Continuing the certified explicit Hopf differential in PR #574. The
algebraic metric identities here apply to the true derivative rows,
which were identified with directional derivatives via HasDerivAt in
HopfSubmersionDifferential20261124. In particular, the identities
characterize the pullback metric on the tangent horizontal distribution
of the unit S³ for the radius-1/2 target.

This is a geometric analytic ingredient of prop:hopf-basic-laplace
and thm:hopf-fefferman-wave. These results do NOT themselves
identify the intrinsic Laplace--Beltrami operators nor establish the
Lorentzian Fefferman wave-operator conjugacy.
-/

namespace Manuscript15.HopfHorizontalIsometry20261124

open Manuscript15.HopfDifferential20261124

/-- Differential of the true rescaled Hopf map h/2 on an
ambient vector v, calculated using its verified Jacobian rows. -/
noncomputable def dHopfBase (q v : HopfQ) : (ℝ × ℝ) × ℝ :=
  ((dot4 (gradX q) v / 2, dot4 (gradY q) v / 2),
    dot4 (gradZ q) v / 2)

/-- Base Euclidean inner product on the three real coordinates. -/
def dot3 (v w : (ℝ × ℝ) × ℝ) : ℝ :=
  v.1.1 * w.1.1 + v.1.2 * w.1.2 + v.2 * w.2

/-- The true unrescaled Hopf differential has an exact full bilinear
energy identity at *every* point of ℝ⁴ (not just S³). The only
null direction for nonzero q is the Hopf-circle generator K(q). -/
theorem differential_metric_identity (q v w : HopfQ) :
    dot4 (gradX q) v * dot4 (gradX q) w +
      dot4 (gradY q) v * dot4 (gradY q) w +
      dot4 (gradZ q) v * dot4 (gradZ q) w =
    4 * normSq4 q * dot4 v w -
      4 * dot4 (verticalGenerator q) v * dot4 (verticalGenerator q) w := by
  dsimp [dot4, gradX, gradY, gradZ, verticalGenerator, normSq4]
  ring

/-- Quadratic consequence: the Hopf differential energy is the
ambient Euclidean energy minus the vertical-circle component. -/
theorem differential_energy_identity (q v : HopfQ) :
    dot4 (gradX q) v ^ 2 +
      dot4 (gradY q) v ^ 2 +
      dot4 (gradZ q) v ^ 2 =
    4 * normSq4 q * dot4 v v -
      4 * dot4 (verticalGenerator q) v ^ 2 := by
  simpa only [pow_two, mul_assoc] using differential_metric_identity q v v

/-- Tangential vectors orthogonal to the vertical Hopf-circle
generator are preserved isometrically by the derivative of h/2
on the unit S³, with no differentiability assumption on an
unrelated function. -/
theorem horizontal_metric_isometry
    (q v w : HopfQ) (hq : normSq4 q = 1)
    (hv : dot4 (verticalGenerator q) v = 0)
    (hw : dot4 (verticalGenerator q) w = 0) :
    dot3 (dHopfBase q v) (dHopfBase q w) = dot4 v w := by
  have h := differential_metric_identity q v w
  rw [hq, hv, hw] at h
  dsimp [dot3, dHopfBase]
  nlinarith

/-- Squared length of an individual horizontal vector is preserved. -/
theorem horizontal_length_isometry
    (q v : HopfQ) (hq : normSq4 q = 1)
    (hv : dot4 (verticalGenerator q) v = 0) :
    dot3 (dHopfBase q v) (dHopfBase q v) = dot4 v v := by
  exact horizontal_metric_isometry q v v hq hv hv

/-- The actual Euler homogeneity identity for the quadratic Hopf map:
h(q)·Dh(q)v = 2|q|² q·v. It identifies the differential of
the sphere constraint rather than merely the mode eigenvalues. -/
theorem radial_image_identity (q v : HopfQ) :
    hopfX q * dot4 (gradX q) v +
      hopfY q * dot4 (gradY q) v +
      hopfZ q * dot4 (gradZ q) v =
    2 * normSq4 q * dot4 q v := by
  dsimp [hopfX, hopfY, hopfZ, gradX, gradY, gradZ, dot4, normSq4]
  ring

/-- The Hopf differential of a tangent vector on the unit S³ is
tangent to the radius-1/2 sphere in the Fubini--Study base.
Together with horizontal_metric_isometry this gives the explicit
pointwise Riemannian-submersion differential data. -/
theorem image_tangent_to_base_sphere
    (q v : HopfQ) (hq : normSq4 q = 1)
    (hqt : dot4 q v = 0) :
    dot3 (hopfBase q) (dHopfBase q v) = 0 := by
  have h := radial_image_identity q v
  rw [hq, hqt] at h
  dsimp [dot3, hopfBase, dHopfBase]
  nlinarith

/-- A vertical vector is sent to zero by the *actual*
differential, not just by its restriction to scalar modes. -/
theorem differential_kills_fibre (q : HopfQ) :
    dHopfBase q (verticalGenerator q) = ((0, 0), 0) := by
  dsimp [dHopfBase]
  rw [gradX_vertical_zero, gradY_vertical_zero, gradZ_vertical_zero]
  norm_num

#print axioms Manuscript15.HopfHorizontalIsometry20261124.differential_metric_identity
#print axioms Manuscript15.HopfHorizontalIsometry20261124.differential_energy_identity
#print axioms Manuscript15.HopfHorizontalIsometry20261124.horizontal_metric_isometry
#print axioms Manuscript15.HopfHorizontalIsometry20261124.horizontal_length_isometry
#print axioms Manuscript15.HopfHorizontalIsometry20261124.radial_image_identity
#print axioms Manuscript15.HopfHorizontalIsometry20261124.image_tangent_to_base_sphere
#print axioms Manuscript15.HopfHorizontalIsometry20261124.differential_kills_fibre

end Manuscript15.HopfHorizontalIsometry20261124
