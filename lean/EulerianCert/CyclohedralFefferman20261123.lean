import Mathlib

/-!
Manuscript 17, 23 November 2026, Fefferman metric on the critical Cassini lobes.
Source ZIP SHA-256: 37a638922cf9f2ff5338e642b794580d825e771b10de7103a48dde143a6306fc.

Exact rational metric factors and dimension-two conformal density cancellation.
No geometric immersion, Laplace--Beltrami operator or pullback metric is
constructed in this file.
-/
namespace EulerianCert.CyclohedralFefferman20261123

def tNu (nu : ℝ) : ℝ := nu / (2 - nu ^ 2)

def affineRoundFactor (nu : ℝ) : ℝ := nu ^ 2 / (2 - nu ^ 2) ^ 2

def feffermanAffineFactor (t : ℝ) : ℝ := 1 / (2 * (1 + t ^ 2))

def quartic (nu : ℝ) : ℝ := nu ^ 4 - 3 * nu ^ 2 + 4

theorem quartic_square_identity (nu : ℝ) :
    quartic nu = (nu ^ 2 - (3 / 2 : ℝ)) ^ 2 + 7 / 4 := by
  unfold quartic
  ring

theorem quartic_positive (nu : ℝ) : 0 < quartic nu := by
  rw [quartic_square_identity]
  positivity

theorem hemisphere_denominator_identity (nu : ℝ) :
    (2 - nu ^ 2) ^ 2 + nu ^ 2 = quartic nu := by
  unfold quartic
  ring

theorem fefferman_factor_positive (t : ℝ) :
    0 < feffermanAffineFactor t := by
  unfold feffermanAffineFactor
  positivity

/-- Equality of the two explicitly displayed Cassini metric coefficients. -/
theorem fefferman_hemisphere_coefficient (nu : ℝ)
    (hchart : 2 - nu ^ 2 ≠ 0) :
    feffermanAffineFactor (tNu nu) * affineRoundFactor nu =
      nu ^ 2 / (2 * quartic nu) := by
  have hq : quartic nu ≠ 0 := (quartic_positive nu).ne'
  have hpos : 1 + (nu / (2 - nu ^ 2)) ^ 2 ≠ 0 := by positivity
  unfold feffermanAffineFactor tNu affineRoundFactor
  field_simp [hchart, hq, hpos, quartic]
  ring

/-- In dimension two, inverse-metric and area factors cancel pointwise. -/
theorem conformal_dirichlet_density (Lambda energy area : ℝ)
    (hLambda : Lambda ≠ 0) :
    (energy / Lambda) * (Lambda * area) = energy * area := by
  field_simp [hLambda]

/-- Algebraic multiplier appearing in the scalar Laplacian formula. -/
theorem conformal_laplacian_multiplier (t delta : ℝ) :
    delta / feffermanAffineFactor t = 2 * (1 + t ^ 2) * delta := by
  unfold feffermanAffineFactor
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [ht]
  ring

#print axioms EulerianCert.CyclohedralFefferman20261123.quartic_square_identity
#print axioms EulerianCert.CyclohedralFefferman20261123.quartic_positive
#print axioms EulerianCert.CyclohedralFefferman20261123.hemisphere_denominator_identity
#print axioms EulerianCert.CyclohedralFefferman20261123.fefferman_factor_positive
#print axioms EulerianCert.CyclohedralFefferman20261123.fefferman_hemisphere_coefficient
#print axioms EulerianCert.CyclohedralFefferman20261123.conformal_dirichlet_density
#print axioms EulerianCert.CyclohedralFefferman20261123.conformal_laplacian_multiplier
end EulerianCert.CyclohedralFefferman20261123
