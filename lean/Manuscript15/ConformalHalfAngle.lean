/-
Manuscript 15 — exact conformal half-angle chart values.

Elementary real statements extracted from Proposition 3.1:
Omega(q)=2*arctan(q), its inverse tan(Omega(q)/2)=q,
and its distinguished points q=1/2 and q=1/pi.

This module deliberately does not claim to formalise Minkowski's
projective null-cone representation or complex Cayley coordinates.
-/
import EulerianCert.Corner
import Mathlib

open Real
noncomputable section
namespace Manuscript15

/-- Principal inverse half-angle parametrisation of the chart. -/
def conformalOmega (q : ℝ) : ℝ := 2 * Real.arctan q

/-- The half-angle tangent recovers the original real chart coordinate. -/
theorem conformalOmega_tan_half (q : ℝ) :
    Real.tan (conformalOmega q / 2) = q := by
  unfold conformalOmega
  have h : (2 * Real.arctan q) / 2 = Real.arctan q := by ring
  rw [h, Real.tan_arctan]

theorem conformalOmega_zero : conformalOmega 0 = 0 := by
  simp [conformalOmega]

theorem conformalOmega_neg (q : ℝ) :
    conformalOmega (-q) = -conformalOmega q := by
  simp [conformalOmega, Real.arctan_neg]
  ring

/-- The source special point q=1/2 is precisely the normalized
    Plouffe/Gregory angle p_gamma = atan(1/2)/pi. -/
theorem conformalOmega_plouffe :
    conformalOmega (1 / 2) / (2 * Real.pi) =
      Real.arctan (1 / 2) / Real.pi := by
  unfold conformalOmega
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
  <;> ring

/-- The point q=1/pi gives the *inherited* Manuscript 11
    Eulerian tangent-corner angle, not a new definition. -/
theorem conformalOmega_eulerian :
    conformalOmega (1 / Real.pi) = EulerianCert.Corner.varthetaE := by
  rfl

#print axioms Manuscript15.conformalOmega_tan_half
#print axioms Manuscript15.conformalOmega_zero
#print axioms Manuscript15.conformalOmega_neg
#print axioms Manuscript15.conformalOmega_plouffe
#print axioms Manuscript15.conformalOmega_eulerian

end Manuscript15
