import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Subsection 9.2: a normalised inverse-tangent function

Manuscript V173, eqs. (177)–(179).
With `s(t) = 2R arctan(t/(2R))`, the dimensionless function
`σ(τ) = s(Rτ)/(2R) = arctan(τ/2)` satisfies
`2σ(1) = 2 arctan(1/2) = 2 arccot 2` and `2σ(2/π) = 2 arctan(1/π) = 2 arccot π = ϑ_E`.
`arccot x` is taken as `π/2 - arctan x` (principal branch); for `x > 0` it equals `arctan (1/x)`.
-/

open Real

namespace EulerianBridge.InverseTangent

/-- Principal inverse cotangent, `arccot x = π/2 - arctan x`. -/
noncomputable def arccot (x : ℝ) : ℝ := π / 2 - arctan x

theorem arccot_eq_arctan_inv {x : ℝ} (hx : 0 < x) : arccot x = arctan (1 / x) := by
  unfold arccot
  rw [one_div, arctan_inv_of_pos hx]

/-- Jadczyk's variable relation `s(t) = 2R arctan(t/(2R))`. -/
noncomputable def sJ (R t : ℝ) : ℝ := 2 * R * arctan (t / (2 * R))

/-- The dimensionless function `σ(τ) := s(Rτ)/(2R)`. -/
noncomputable def sigma (R τ : ℝ) : ℝ := sJ R (R * τ) / (2 * R)

/-- Eq. (177): `σ(τ) = arctan(τ/2)`, independently of `R > 0`. -/
theorem sigma_eq {R : ℝ} (hR : 0 < R) (τ : ℝ) : sigma R τ = arctan (τ / 2) := by
  unfold sigma sJ
  have hR' : R ≠ 0 := hR.ne'
  have : R * τ / (2 * R) = τ / 2 := by field_simp
  rw [this]
  field_simp

/-- Eq. (178): `2σ(1) = 2 arctan(1/2) = 2 arccot 2`. -/
theorem two_sigma_one {R : ℝ} (hR : 0 < R) :
    2 * sigma R 1 = 2 * arctan (1 / 2) ∧ 2 * arctan (1 / 2) = 2 * arccot 2 := by
  refine ⟨by rw [sigma_eq hR], ?_⟩
  rw [arccot_eq_arctan_inv (by norm_num : (0:ℝ) < 2)]

/-- The Eulerian endpoint angle `ϑ_E = 2 arctan(1/π)`. -/
noncomputable def varthetaE : ℝ := 2 * arctan (1 / π)

/-- Eq. (179): `ϑ_E = 2σ(2/π) = 2 arctan(1/π) = 2 arccot π`. -/
theorem varthetaE_eq {R : ℝ} (hR : 0 < R) :
    varthetaE = 2 * sigma R (2 / π) ∧ varthetaE = 2 * arccot π := by
  refine ⟨?_, ?_⟩
  · rw [sigma_eq hR]
    unfold varthetaE
    congr 2
    field_simp
  · unfold varthetaE
    rw [arccot_eq_arctan_inv pi_pos]

end EulerianBridge.InverseTangent
