import SpecialImaginaryPoint.V14119Priority3ComplexDirichletSinhEntire

/-!
# Manuscript 15 — ENTIRE cycloidal curvature-radius / genuine CFC-S₁ Dirichlet determinant bridge

The complex analytic continuation of the cycloid curvature radius is
  R_a(w) = 4a sin(w/2).

For arbitrary COMPLEX scale a and spectral parameter z, including
zero, the ACTUAL universal trace-class Dirichlet inverse Fredholm
determinant satisfies the DIVISION-FREE, ENTIRE identity

  4 a i z det_F(I+z² A_D⁻¹) = R_a(2 i z).

This is NOT a definition of the determinant: the function on the left
is the already kernel-certified genuine CFC Schatten-S₁ Fredholm
determinant of the actual l² Dirichlet inverse spectral operator,
constructed from finite Hilbert compression determinants. It is
not the zeta-regularized determinant of an unbounded operator.

For nonzero a,z, the corresponding exact cycloidal-radius quotient
identity follows. The zero case is included in the entire identity.
-/

noncomputable section

namespace Manuscript14Priority3.CycloidalRadiusUniversalDirichlet

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.ComplexDirichletSinhEntire

/-- Entire complex cycloidal continuation of the curvature-radius
formula R_a(w)=4a sin(w/2). -/
def analyticCycloidRadius (a w : ℂ) : ℂ :=
  4 * a * Complex.sin (w / 2)

/-- Division-free ENTIRE identity linking the complex cycloidal
curvature-radius function and the true universal Dirichlet inverse
CFC Schatten-S₁ Fredholm determinant for all a,z∈ℂ. -/
theorem universal_dirichlet_cycloid_radius_entire
    (a z : ℂ) :
    (4 * a * Complex.I * z) *
        fredholmDet inverseTraceClass (z ^ 2) =
      analyticCycloidRadius a (2 * z * Complex.I) := by
  have h := universal_dirichlet_sinh_entire_identity z
  have hhalf : (2 * z * Complex.I) / 2 =
      z * Complex.I := by ring
  unfold analyticCycloidRadius
  rw [hhalf, Complex.sin_mul_I]
  calc
    (4 * a * Complex.I * z) *
        fredholmDet inverseTraceClass (z ^ 2) =
      (4 * a * Complex.I) *
        (z * fredholmDet inverseTraceClass (z ^ 2)) := by ring
    _ = (4 * a * Complex.I) * Complex.sinh z := by rw [h]
    _ = 4 * a * (Complex.sinh z * Complex.I) := by ring

/-- For a≠0 and z≠0, the universal Dirichlet determinant is
exactly the analytically continued cycloidal radius quotient. -/
theorem universal_dirichlet_cycloid_radius_quotient
    (a z : ℂ) (ha : a ≠ 0) (hz : z ≠ 0) :
    fredholmDet inverseTraceClass (z ^ 2) =
      analyticCycloidRadius a (2 * z * Complex.I) /
        (4 * a * Complex.I * z) := by
  have hden : (4 * a * Complex.I * z) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) ha)
        Complex.I_ne_zero)
      hz
  apply (eq_div_iff hden).2
  calc
    fredholmDet inverseTraceClass (z ^ 2) *
        (4 * a * Complex.I * z) =
      (4 * a * Complex.I * z) *
        fredholmDet inverseTraceClass (z ^ 2) := mul_comm _ _
    _ = analyticCycloidRadius a (2 * z * Complex.I) :=
      universal_dirichlet_cycloid_radius_entire a z

#print axioms Manuscript14Priority3.CycloidalRadiusUniversalDirichlet.universal_dirichlet_cycloid_radius_entire
#print axioms Manuscript14Priority3.CycloidalRadiusUniversalDirichlet.universal_dirichlet_cycloid_radius_quotient

end Manuscript14Priority3.CycloidalRadiusUniversalDirichlet
