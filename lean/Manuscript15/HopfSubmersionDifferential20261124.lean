import Mathlib

/-!
# Manuscript 15 — explicit differential geometry of the Hopf map (24 Nov 2026)

Source: Manuscript_15_20261124_EDITORIALE_EQUAZIONI_COMPLETE(1).zip
SHA256 ZIP: e9dea5546bca52a3a88001c3e29c4caa7ac62325446a30c3b0fa54a2aa9d2acd
SHA256 15.tex: e3b6632886cf881c46decf051f19169486229b4168fe97fb011398e38ee4b396

This file treats the actual quadratic Hopf map on the ambient real
coordinates of ℂ², not a hypothetical map with an assumed Laplacian
intertwining property.

Write z₁=a+ib, z₂=c+id. The map is
  h(z₁,z₂) = (2 Re(z₁ conj(z₂)), 2 Im(z₁ conj(z₂)), |z₁|²-|z₂|²).
Its squared norm is |(z₁,z₂)|⁴. Its differential has pairwise
orthogonal rows with squared length 4 |(z₁,z₂)|²; after division by
two, these are unit horizontal co-gradients on the unit S³. The
circle action simultaneously rotating both complex coordinates
preserves h exactly.

The full Riemannian-submersion theorem and Laplace--Beltrami
intertwining on S³/CP¹, as well as the Fefferman wave-operator
conjugacy, require subsequent manifold/operator theorems. This
module does *not* claim to have formalised them.
-/

namespace Manuscript15.HopfDifferential20261124

/-- Real coordinates ((Re z₁, Im z₁), (Re z₂, Im z₂)). -/
abbrev HopfQ := (ℝ × ℝ) × (ℝ × ℝ)

/-- Ambient squared Euclidean norm on ℂ² ≅ ℝ⁴. -/
def normSq4 (q : HopfQ) : ℝ :=
  q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

/-- First Cartesian coordinate 2 Re(z₁ conj z₂). -/
def hopfX (q : HopfQ) : ℝ :=
  2 * (q.1.1 * q.2.1 + q.1.2 * q.2.2)

/-- Second Cartesian coordinate 2 Im(z₁ conj z₂). -/
def hopfY (q : HopfQ) : ℝ :=
  2 * (q.1.2 * q.2.1 - q.1.1 * q.2.2)

/-- Third Cartesian coordinate |z₁|² - |z₂|². -/
def hopfZ (q : HopfQ) : ℝ :=
  q.1.1 ^ 2 + q.1.2 ^ 2 - q.2.1 ^ 2 - q.2.2 ^ 2

/-- The Hopf map into the unit-radius sphere, in ambient coordinates. -/
def hopfMap (q : HopfQ) : (ℝ × ℝ) × ℝ :=
  ((hopfX q, hopfY q), hopfZ q)

/-- Actual curvature-4 sphere coordinates: the map rescaled by 1/2. -/
noncomputable def hopfBase (q : HopfQ) : (ℝ × ℝ) × ℝ :=
  ((hopfX q / 2, hopfY q / 2), hopfZ q / 2)

/-- The quadratic Hopf identity, for every q in the ambient ℝ⁴. -/
theorem hopf_norm_identity (q : HopfQ) :
    hopfX q ^ 2 + hopfY q ^ 2 + hopfZ q ^ 2 = (normSq4 q) ^ 2 := by
  dsimp [hopfX, hopfY, hopfZ, normSq4]
  ring

/-- For q on the unit sphere, the rescaled image lies on the
radius-1/2 sphere, the Fubini--Study base's metric normalisation. -/
theorem hopf_base_radius_half (q : HopfQ) (hq : normSq4 q = 1) :
    (hopfBase q).1.1 ^ 2 + (hopfBase q).1.2 ^ 2 +
      (hopfBase q).2 ^ 2 = (1 / 4 : ℝ) := by
  have h := hopf_norm_identity q
  rw [hq] at h
  dsimp [hopfBase]
  nlinarith

/-- Euclidean bilinear form on ℝ⁴. -/
def dot4 (v w : HopfQ) : ℝ :=
  v.1.1 * w.1.1 + v.1.2 * w.1.2 +
    v.2.1 * w.2.1 + v.2.2 * w.2.2

/-- Row of the real Jacobian of the first Hopf coordinate. -/
def gradX (q : HopfQ) : HopfQ :=
  ((2 * q.2.1, 2 * q.2.2), (2 * q.1.1, 2 * q.1.2))

/-- Row of the real Jacobian of the second Hopf coordinate. -/
def gradY (q : HopfQ) : HopfQ :=
  ((-2 * q.2.2, 2 * q.2.1), (2 * q.1.2, -2 * q.1.1))

/-- Row of the real Jacobian of the third Hopf coordinate. -/
def gradZ (q : HopfQ) : HopfQ :=
  ((2 * q.1.1, 2 * q.1.2), (-2 * q.2.1, -2 * q.2.2))

/-- The X Jacobian row has squared length 4 |q|². -/
theorem gram_xx (q : HopfQ) :
    dot4 (gradX q) (gradX q) = 4 * normSq4 q := by
  dsimp [dot4, gradX, normSq4]
  ring

/-- The Y Jacobian row has squared length 4 |q|². -/
theorem gram_yy (q : HopfQ) :
    dot4 (gradY q) (gradY q) = 4 * normSq4 q := by
  dsimp [dot4, gradY, normSq4]
  ring

/-- The Z Jacobian row has squared length 4 |q|². -/
theorem gram_zz (q : HopfQ) :
    dot4 (gradZ q) (gradZ q) = 4 * normSq4 q := by
  dsimp [dot4, gradZ, normSq4]
  ring

/-- The X/Y rows of the Hopf differential are orthogonal. -/
theorem gram_xy (q : HopfQ) :
    dot4 (gradX q) (gradY q) = 0 := by
  dsimp [dot4, gradX, gradY]
  ring

/-- The X/Z rows of the Hopf differential are orthogonal. -/
theorem gram_xz (q : HopfQ) :
    dot4 (gradX q) (gradZ q) = 0 := by
  dsimp [dot4, gradX, gradZ]
  ring

/-- The Y/Z rows of the Hopf differential are orthogonal. -/
theorem gram_yz (q : HopfQ) :
    dot4 (gradY q) (gradZ q) = 0 := by
  dsimp [dot4, gradY, gradZ]
  ring

/-- The horizontal differential of the rescaled map has unit
co-gradient norm at every point of the unit S³. -/
theorem horizontal_unit_x (q : HopfQ) (hq : normSq4 q = 1) :
    dot4 (gradX q) (gradX q) / 4 = 1 := by
  rw [gram_xx, hq]
  ring

/-- The scalar horizontal metric identity for the rescaled Y row. -/
theorem horizontal_unit_y (q : HopfQ) (hq : normSq4 q = 1) :
    dot4 (gradY q) (gradY q) / 4 = 1 := by
  rw [gram_yy, hq]
  ring

/-- The scalar horizontal metric identity for the rescaled Z row. -/
theorem horizontal_unit_z (q : HopfQ) (hq : normSq4 q = 1) :
    dot4 (gradZ q) (gradZ q) / 4 = 1 := by
  rw [gram_zz, hq]
  ring

/-- Simultaneous rotation of z₁ and z₂ by c+is in real coordinates. -/
def phaseRotate (c s : ℝ) (q : HopfQ) : HopfQ :=
  ((c * q.1.1 - s * q.1.2, s * q.1.1 + c * q.1.2),
   (c * q.2.1 - s * q.2.2, s * q.2.1 + c * q.2.2))

/-- Hopf X scales with |c+is|² under common phase rotation. -/
theorem hopfX_phaseRotate (c s : ℝ) (q : HopfQ) :
    hopfX (phaseRotate c s q) = (c ^ 2 + s ^ 2) * hopfX q := by
  dsimp [hopfX, phaseRotate]
  ring

/-- Hopf Y scales with |c+is|² under common phase rotation. -/
theorem hopfY_phaseRotate (c s : ℝ) (q : HopfQ) :
    hopfY (phaseRotate c s q) = (c ^ 2 + s ^ 2) * hopfY q := by
  dsimp [hopfY, phaseRotate]
  ring

/-- Hopf Z scales with |c+is|² under common phase rotation. -/
theorem hopfZ_phaseRotate (c s : ℝ) (q : HopfQ) :
    hopfZ (phaseRotate c s q) = (c ^ 2 + s ^ 2) * hopfZ q := by
  dsimp [hopfZ, phaseRotate]
  ring

/-- Common unit-circle phase rotation fixes the *actual Hopf map*,
not merely its eigenvalue arithmetic. -/
theorem hopfMap_phase_invariant (c s : ℝ) (q : HopfQ)
    (h : c ^ 2 + s ^ 2 = 1) :
    hopfMap (phaseRotate c s q) = hopfMap q := by
  simp only [hopfMap, hopfX_phaseRotate, hopfY_phaseRotate,
    hopfZ_phaseRotate, h, one_mul]

/-- The unit-circle phase rotation preserves the ambient S³. -/
theorem normSq4_phaseRotate (c s : ℝ) (q : HopfQ) :
    normSq4 (phaseRotate c s q) =
      (c ^ 2 + s ^ 2) * normSq4 q := by
  dsimp [normSq4, phaseRotate]
  ring

/-- The antipodal map acts within each Hopf fibre. -/
theorem hopfMap_antipodal (q : HopfQ) :
    hopfMap (phaseRotate (-1) 0 q) = hopfMap q := by
  apply hopfMap_phase_invariant
  norm_num

/-- Affine line in the ambient ℝ⁴, to check the actual derivatives
of the quadratic Hopf-coordinate functions. -/
def affineLine (q v : HopfQ) (t : ℝ) : HopfQ :=
  ((q.1.1 + t * v.1.1, q.1.2 + t * v.1.2),
   (q.2.1 + t * v.2.1, q.2.2 + t * v.2.2))

private theorem affineCoordinate_hasDerivAt (x v t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s * v) v t := by
  simpa using ((hasDerivAt_id t).mul_const v).const_add x

/-- The first Hopf-coordinate Jacobian row is its *actual*
directional derivative along every affine line, at every time. -/
theorem hopfX_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hopfX (affineLine q v s))
      (dot4 (gradX (affineLine q v t)) v) t := by
  have ha := affineCoordinate_hasDerivAt q.1.1 v.1.1 t
  have hb := affineCoordinate_hasDerivAt q.1.2 v.1.2 t
  have hc := affineCoordinate_hasDerivAt q.2.1 v.2.1 t
  have hd := affineCoordinate_hasDerivAt q.2.2 v.2.2 t
  have h := ((ha.mul hc).add (hb.mul hd)).const_mul 2
  convert h using 1 <;> simp [hopfX, affineLine, dot4, gradX] <;> ring

/-- The second Hopf-coordinate Jacobian row is the actual
directional derivative at every point of every affine line. -/
theorem hopfY_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hopfY (affineLine q v s))
      (dot4 (gradY (affineLine q v t)) v) t := by
  have ha := affineCoordinate_hasDerivAt q.1.1 v.1.1 t
  have hb := affineCoordinate_hasDerivAt q.1.2 v.1.2 t
  have hc := affineCoordinate_hasDerivAt q.2.1 v.2.1 t
  have hd := affineCoordinate_hasDerivAt q.2.2 v.2.2 t
  have h := ((hb.mul hc).sub (ha.mul hd)).const_mul 2
  convert h using 1 <;> simp [hopfY, affineLine, dot4, gradY] <;> ring

/-- The third Hopf-coordinate Jacobian row is the actual
directional derivative at every point of every affine line. -/
theorem hopfZ_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hopfZ (affineLine q v s))
      (dot4 (gradZ (affineLine q v t)) v) t := by
  have ha := affineCoordinate_hasDerivAt q.1.1 v.1.1 t
  have hb := affineCoordinate_hasDerivAt q.1.2 v.1.2 t
  have hc := affineCoordinate_hasDerivAt q.2.1 v.2.1 t
  have hd := affineCoordinate_hasDerivAt q.2.2 v.2.2 t
  have h := (((ha.pow 2).add (hb.pow 2)).sub (hc.pow 2)).sub (hd.pow 2)
  have hfun :
      (fun s : ℝ => hopfZ (affineLine q v s)) =
        ((fun s : ℝ => q.1.1 + s * v.1.1) ^ 2 +
          (fun s : ℝ => q.1.2 + s * v.1.2) ^ 2 -
          (fun s : ℝ => q.2.1 + s * v.2.1) ^ 2 -
          (fun s : ℝ => q.2.2 + s * v.2.2) ^ 2) := by
    funext s
    simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
    dsimp [hopfZ, affineLine]
  rw [← hfun] at h
  convert h using 1 <;> simp [dot4, gradZ, affineLine] <;> ring

#print axioms Manuscript15.HopfDifferential20261124.hopf_norm_identity
#print axioms Manuscript15.HopfDifferential20261124.hopf_base_radius_half
#print axioms Manuscript15.HopfDifferential20261124.gram_xx
#print axioms Manuscript15.HopfDifferential20261124.gram_yy
#print axioms Manuscript15.HopfDifferential20261124.gram_zz
#print axioms Manuscript15.HopfDifferential20261124.gram_xy
#print axioms Manuscript15.HopfDifferential20261124.gram_xz
#print axioms Manuscript15.HopfDifferential20261124.gram_yz
#print axioms Manuscript15.HopfDifferential20261124.horizontal_unit_x
#print axioms Manuscript15.HopfDifferential20261124.horizontal_unit_y
#print axioms Manuscript15.HopfDifferential20261124.horizontal_unit_z
#print axioms Manuscript15.HopfDifferential20261124.hopfX_phaseRotate
#print axioms Manuscript15.HopfDifferential20261124.hopfY_phaseRotate
#print axioms Manuscript15.HopfDifferential20261124.hopfZ_phaseRotate
#print axioms Manuscript15.HopfDifferential20261124.hopfMap_phase_invariant
#print axioms Manuscript15.HopfDifferential20261124.normSq4_phaseRotate
#print axioms Manuscript15.HopfDifferential20261124.hopfMap_antipodal
#print axioms Manuscript15.HopfDifferential20261124.hopfX_hasDerivAt_affineLine
#print axioms Manuscript15.HopfDifferential20261124.hopfY_hasDerivAt_affineLine
#print axioms Manuscript15.HopfDifferential20261124.hopfZ_hasDerivAt_affineLine

end Manuscript15.HopfDifferential20261124
