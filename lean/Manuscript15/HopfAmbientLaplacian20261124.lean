import Manuscript15.HopfHorizontalIsometry20261124
import Mathlib

/-!
# M15: actual second-order Laplacian symbol of the Hopf map

Source: Manuscript_15_20261124_EDITORIALE_EQUAZIONI_COMPLETE(1).zip
ZIP SHA256 e9dea5546bca52a3a88001c3e29c4caa7ac62325446a30c3b0fa54a2aa9d2acd
15.tex SHA256 e3b6632886cf881c46decf051f19169486229b4168fe97fb011398e38ee4b396

Necessary analytic jet step in Proposition prop:hopf-basic-laplace:
The TRUE rescaled Hopf map h/2 : ℝ⁴ → ℝ³ has harmonic coordinate
functions, and its Jacobian satisfies D(h/2) D(h/2)^T = |q|² I₃.
Thus its Hessian contraction against ANY symmetric base 2-jet is
|q|² times the Euclidean base Hessian trace. The proofs below use
actual real-directional HasDerivAt, not hypothetical operators.

This file does not claim the full theorem for arbitrary smooth f on
CP¹: identifying the intrinsic sphere Laplace--Beltrami operators
and C² composition chain rule remains an independent obligation.
-/

namespace Manuscript15.HopfAmbientLaplacian20261124

open Manuscript15.HopfDifferential20261124
open Manuscript15.HopfHorizontalIsometry20261124

/-- Actual Euclidean co-gradient of the first RESCALED Hopf coordinate. -/
def rowX (q : HopfQ) : HopfQ :=
  ((q.2.1, q.2.2), (q.1.1, q.1.2))

/-- Actual Euclidean co-gradient of the second RESCALED coordinate. -/
def rowY (q : HopfQ) : HopfQ :=
  ((-q.2.2, q.2.1), (q.1.2, -q.1.1))

/-- Actual Euclidean co-gradient of the third RESCALED coordinate. -/
def rowZ (q : HopfQ) : HopfQ :=
  ((q.1.1, q.1.2), (-q.2.1, -q.2.2))

theorem rowX_sq (q : HopfQ) :
    dot4 (rowX q) (rowX q) = normSq4 q := by
  dsimp [dot4, rowX, normSq4]; ring

theorem rowY_sq (q : HopfQ) :
    dot4 (rowY q) (rowY q) = normSq4 q := by
  dsimp [dot4, rowY, normSq4]; ring

theorem rowZ_sq (q : HopfQ) :
    dot4 (rowZ q) (rowZ q) = normSq4 q := by
  dsimp [dot4, rowZ, normSq4]; ring

theorem rowXY_orthogonal (q : HopfQ) :
    dot4 (rowX q) (rowY q) = 0 := by
  dsimp [dot4, rowX, rowY]; ring

theorem rowXZ_orthogonal (q : HopfQ) :
    dot4 (rowX q) (rowZ q) = 0 := by
  dsimp [dot4, rowX, rowZ]; ring

theorem rowYZ_orthogonal (q : HopfQ) :
    dot4 (rowY q) (rowZ q) = 0 := by
  dsimp [dot4, rowY, rowZ]; ring

/-- Full contraction of an arbitrary symmetric 3×3 Hessian jet
with the *actual* real Hopf Jacobian. The off-diagonal jets
are retained and cancelled rigorously, not omitted. -/
def baseHessianContraction (q : HopfQ)
    (hxx hxy hxz hyy hyz hzz : ℝ) : ℝ :=
  hxx * dot4 (rowX q) (rowX q) +
    2 * hxy * dot4 (rowX q) (rowY q) +
    2 * hxz * dot4 (rowX q) (rowZ q) +
    hyy * dot4 (rowY q) (rowY q) +
    2 * hyz * dot4 (rowY q) (rowZ q) +
    hzz * dot4 (rowZ q) (rowZ q)

/-- The complete second-order PRINCIPAL SYMBOL of the Hopf
pullback, valid for all six symmetric Hessian components at
every ambient point, is precisely |q|² times the base trace. -/
theorem hopf_principal_symbol (q : HopfQ)
    (hxx hxy hxz hyy hyz hzz : ℝ) :
    baseHessianContraction q hxx hxy hxz hyy hyz hzz =
      normSq4 q * (hxx + hyy + hzz) := by
  dsimp [baseHessianContraction]
  rw [rowX_sq, rowY_sq, rowZ_sq,
      rowXY_orthogonal, rowXZ_orthogonal, rowYZ_orthogonal]
  ring

/-- On the TRUE unit S³ the principal symbol agrees exactly
with the standard Euclidean trace of the 3D base jet. -/
theorem hopf_principal_symbol_on_sphere (q : HopfQ)
    (hq : normSq4 q = 1)
    (hxx hxy hxz hyy hyz hzz : ℝ) :
    baseHessianContraction q hxx hxy hxz hyy hyz hzz =
      hxx + hyy + hzz := by
  rw [hopf_principal_symbol, hq, one_mul]

/-- Identification of the first actual real directional derivative
of the first base coordinate h_x/2. -/
theorem baseX_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (hopfBase (affineLine q v s)).1.1)
      (dot4 (rowX (affineLine q v t)) v) t := by
  have h := (hopfX_hasDerivAt_affineLine q v t).mul_const (1 / 2 : ℝ)
  convert h using 1
  · funext s
    dsimp [hopfBase]
    ring
  · dsimp [rowX, dot4, gradX]
    ring

/-- As above for the second base coordinate. -/
theorem baseY_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (hopfBase (affineLine q v s)).1.2)
      (dot4 (rowY (affineLine q v t)) v) t := by
  have h := (hopfY_hasDerivAt_affineLine q v t).mul_const (1 / 2 : ℝ)
  convert h using 1
  · funext s
    dsimp [hopfBase]
    ring
  · dsimp [rowY, dot4, gradY]
    ring

/-- As above for the third base coordinate. -/
theorem baseZ_hasDerivAt_affineLine (q v : HopfQ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (hopfBase (affineLine q v s)).2)
      (dot4 (rowZ (affineLine q v t)) v) t := by
  have h := (hopfZ_hasDerivAt_affineLine q v t).mul_const (1 / 2 : ℝ)
  convert h using 1
  · funext s
    dsimp [hopfBase]
    ring
  · dsimp [rowZ, dot4, gradZ]
    ring

/-- Linear dependence on the affine-line parameter of
the first base coordinate's true directional derivative. -/
theorem rowX_dot_affineLine (q v : HopfQ) (t : ℝ) :
    dot4 (rowX (affineLine q v t)) v =
      dot4 (rowX q) v + t * hopfX v := by
  dsimp [dot4, rowX, affineLine, hopfX]; ring

theorem rowY_dot_affineLine (q v : HopfQ) (t : ℝ) :
    dot4 (rowY (affineLine q v t)) v =
      dot4 (rowY q) v + t * hopfY v := by
  dsimp [dot4, rowY, affineLine, hopfY]; ring

theorem rowZ_dot_affineLine (q v : HopfQ) (t : ℝ) :
    dot4 (rowZ (affineLine q v t)) v =
      dot4 (rowZ q) v + t * hopfZ v := by
  dsimp [dot4, rowZ, affineLine, hopfZ]; ring

/-- The true second directional derivative of the rescaled
Hopf X coordinate is the quadratic polar form evaluated at v.
It is independent of q and time. -/
theorem baseX_second_deriv_affineLine (q v : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv
      (fun r : ℝ => (hopfBase (affineLine q v r)).1.1) s) t =
      hopfX v := by
  have hfun :
      (fun s : ℝ => deriv
        (fun r : ℝ => (hopfBase (affineLine q v r)).1.1) s) =
      (fun s : ℝ => dot4 (rowX q) v + s * hopfX v) := by
    funext s
    rw [(baseX_hasDerivAt_affineLine q v s).deriv,
      rowX_dot_affineLine]
  rw [hfun]
  have h := ((hasDerivAt_id t).mul_const (hopfX v)).const_add (dot4 (rowX q) v)
  exact h.deriv

theorem baseY_second_deriv_affineLine (q v : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv
      (fun r : ℝ => (hopfBase (affineLine q v r)).1.2) s) t =
      hopfY v := by
  have hfun :
      (fun s : ℝ => deriv
        (fun r : ℝ => (hopfBase (affineLine q v r)).1.2) s) =
      (fun s : ℝ => dot4 (rowY q) v + s * hopfY v) := by
    funext s
    rw [(baseY_hasDerivAt_affineLine q v s).deriv,
      rowY_dot_affineLine]
  rw [hfun]
  have h := ((hasDerivAt_id t).mul_const (hopfY v)).const_add (dot4 (rowY q) v)
  exact h.deriv

theorem baseZ_second_deriv_affineLine (q v : HopfQ) (t : ℝ) :
    deriv (fun s : ℝ => deriv
      (fun r : ℝ => (hopfBase (affineLine q v r)).2) s) t =
      hopfZ v := by
  have hfun :
      (fun s : ℝ => deriv
        (fun r : ℝ => (hopfBase (affineLine q v r)).2) s) =
      (fun s : ℝ => dot4 (rowZ q) v + s * hopfZ v) := by
    funext s
    rw [(baseZ_hasDerivAt_affineLine q v s).deriv,
      rowZ_dot_affineLine]
  rw [hfun]
  have h := ((hasDerivAt_id t).mul_const (hopfZ v)).const_add (dot4 (rowZ q) v)
  exact h.deriv

/-- The four Euclidean unit directions. -/
def axisA : HopfQ := ((1, 0), (0, 0))
def axisB : HopfQ := ((0, 1), (0, 0))
def axisC : HopfQ := ((0, 0), (1, 0))
def axisD : HopfQ := ((0, 0), (0, 1))

/-- The actual coordinate-axis Euclidean second-derivative trace.
This definition involves true analytic derivatives, not formal jets. -/
noncomputable def ambientCoordTrace (F : HopfQ → ℝ) (q : HopfQ) : ℝ :=
  (deriv (fun s : ℝ => deriv (fun r : ℝ => F (affineLine q axisA r)) s) 0) +
  (deriv (fun s : ℝ => deriv (fun r : ℝ => F (affineLine q axisB r)) s) 0) +
  (deriv (fun s : ℝ => deriv (fun r : ℝ => F (affineLine q axisC r)) s) 0) +
  (deriv (fun s : ℝ => deriv (fun r : ℝ => F (affineLine q axisD r)) s) 0)

/-- The first coordinate of the true rescaled quadratic Hopf map
is Euclidean harmonic on ALL of ℝ⁴. -/
theorem ambient_harmonic_baseX (q : HopfQ) :
    ambientCoordTrace (fun w => (hopfBase w).1.1) q = 0 := by
  unfold ambientCoordTrace
  rw [baseX_second_deriv_affineLine, baseX_second_deriv_affineLine,
      baseX_second_deriv_affineLine, baseX_second_deriv_affineLine]
  norm_num [axisA, axisB, axisC, axisD, hopfX]

/-- The second rescaled Hopf coordinate is Euclidean harmonic. -/
theorem ambient_harmonic_baseY (q : HopfQ) :
    ambientCoordTrace (fun w => (hopfBase w).1.2) q = 0 := by
  unfold ambientCoordTrace
  rw [baseY_second_deriv_affineLine, baseY_second_deriv_affineLine,
      baseY_second_deriv_affineLine, baseY_second_deriv_affineLine]
  norm_num [axisA, axisB, axisC, axisD, hopfY]

/-- The third rescaled Hopf coordinate is Euclidean harmonic;
its four diagonal Hessian entries are 1,1,-1,-1. -/
theorem ambient_harmonic_baseZ (q : HopfQ) :
    ambientCoordTrace (fun w => (hopfBase w).2) q = 0 := by
  unfold ambientCoordTrace
  rw [baseZ_second_deriv_affineLine, baseZ_second_deriv_affineLine,
      baseZ_second_deriv_affineLine, baseZ_second_deriv_affineLine]
  norm_num [axisA, axisB, axisC, axisD, hopfZ]

#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowX_sq
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowY_sq
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowZ_sq
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowXY_orthogonal
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowXZ_orthogonal
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowYZ_orthogonal
#print axioms Manuscript15.HopfAmbientLaplacian20261124.hopf_principal_symbol
#print axioms Manuscript15.HopfAmbientLaplacian20261124.hopf_principal_symbol_on_sphere
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseX_hasDerivAt_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseY_hasDerivAt_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseZ_hasDerivAt_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowX_dot_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowY_dot_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.rowZ_dot_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseX_second_deriv_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseY_second_deriv_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.baseZ_second_deriv_affineLine
#print axioms Manuscript15.HopfAmbientLaplacian20261124.ambient_harmonic_baseX
#print axioms Manuscript15.HopfAmbientLaplacian20261124.ambient_harmonic_baseY
#print axioms Manuscript15.HopfAmbientLaplacian20261124.ambient_harmonic_baseZ

end Manuscript15.HopfAmbientLaplacian20261124
