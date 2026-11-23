import Mathlib

/-!
Manuscript 17, "REFERENCES_REPAIRED_FINAL", §4.3 [Fefferman] and
§4.4 [curvature and finite area]. Algebraic identities from the
displayed positive chart and curvature formulas, not the geometric
Gauss curvature or improper-integral statements.
-/
noncomputable section
namespace EulerianCert.CyclohedralFeffermanCurvature20261123

def curvatureNu (nu : ℝ) : ℝ := 3 + 4 / nu ^ 4
def curvatureRho (rho : ℝ) : ℝ := 4 + 2 / rho ^ 2 + 1 / rho ^ 4

theorem curvature_two_coordinates (nu rho : ℝ)
    (hnu : nu ≠ 0) (hrho : rho ≠ 0)
    (hcoord : nu ^ 2 = 2 * rho ^ 2 / (1 + rho ^ 2)) :
    curvatureNu nu = curvatureRho rho := by
  unfold curvatureNu curvatureRho
  have hden : 1 + rho ^ 2 ≠ 0 := by positivity
  rw [show nu ^ 4 = (nu ^ 2) ^ 2 by ring, hcoord]
  field_simp [hrho, hden]
  ring

/-- A regular lobe with 0 < |nu| ≤ 1 has K ≥ 7. -/
theorem curvature_minimum_bound (nu : ℝ)
    (hnu : nu ≠ 0) (hbound : nu ^ 2 ≤ 1) :
    7 ≤ curvatureNu nu := by
  have hnonneg : 0 ≤ nu ^ 2 := sq_nonneg nu
  have hp : 0 < nu ^ 4 := by
    calc
      0 < (nu ^ 2) ^ 2 := pow_pos (sq_pos_of_ne_zero hnu) 2
      _ = nu ^ 4 := by ring
  have hle : nu ^ 4 ≤ 1 := by
    have hmul : 0 ≤ nu ^ 2 * (1 - nu ^ 2) :=
      mul_nonneg hnonneg (by linarith)
    nlinarith
  have hd : 4 ≤ 4 / nu ^ 4 :=
    (le_div_iff₀ hp).2 (by nlinarith)
  unfold curvatureNu
  linarith

theorem curvature_pole : curvatureNu 1 = 7 := by
  norm_num [curvatureNu]

/-- Curvature factor in the proof via conformal Laplacian numerator.
The actual formula for Δ_rd(log|nu| - log(2-nu²)) is geometric analysis. -/
theorem curvature_rational_factor (nu : ℝ)
    (hnu : nu ≠ 0) (hchart : 2 - nu ^ 2 ≠ 0) :
    ((2 - nu ^ 2) ^ 2 / nu ^ 2) *
      ((3 * nu ^ 4 + 4) / (nu ^ 2 * (2 - nu ^ 2) ^ 2)) =
      curvatureNu nu := by
  unfold curvatureNu
  field_simp [hnu, hchart]

/-- Normalizing the polynomial null lift by a common positive radius
puts the real-imaginary time pair and the spatial four-vector on unit
spheres. This proves the stated component norm equations, not smoothness
or the geometric embedding itself. -/
theorem normalized_null_lift (t y z rho R : ℝ)
    (hnull : y ^ 2 + z ^ 2 + rho ^ 4 + 1 = t ^ 2 + 1)
    (hR : R ^ 2 = t ^ 2 + 1)
    (hRn : R ≠ 0) :
    (t / R) ^ 2 + (1 / R) ^ 2 = 1 ∧
    (y / R) ^ 2 + (z / R) ^ 2 + (rho ^ 2 / R) ^ 2 +
      (1 / R) ^ 2 = 1 := by
  constructor
  · field_simp [hRn] <;> nlinarith [hR]
  · field_simp [hRn] <;> nlinarith [hR, hnull]

#print axioms EulerianCert.CyclohedralFeffermanCurvature20261123.curvature_two_coordinates
#print axioms EulerianCert.CyclohedralFeffermanCurvature20261123.curvature_minimum_bound
#print axioms EulerianCert.CyclohedralFeffermanCurvature20261123.curvature_pole
#print axioms EulerianCert.CyclohedralFeffermanCurvature20261123.curvature_rational_factor
#print axioms EulerianCert.CyclohedralFeffermanCurvature20261123.normalized_null_lift
end EulerianCert.CyclohedralFeffermanCurvature20261123
