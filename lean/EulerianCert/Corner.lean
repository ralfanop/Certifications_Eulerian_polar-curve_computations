/-
# Propositions 3.6–3.7 of the V478 manuscript: derivatives of `r_E`, the corner, curvature sign

* `r_E(θ) = 2 sin(θ/2)/θ` (θ ≠ 0): first and second derivatives (proof of Prop. 3.6 and the
  `r''` used in Eq. 40), the endpoint values `r_E(π) = 2/π`, `r_E'(π) = -2/π²` (Eqs. 30–31).
* Eq. (40): `r² + 2r'² - r r'' = (3θ sin²(θ/2) + 2(θ - sin θ))/θ³ > 0` for `θ > 0`.
* One-sided tangents at `θ = π` (Eq. 32) and the corner (Eq. 33): `tan(ϑ_E/2) = 1/π` with
  `ϑ_E = 2 arctan(1/π) = 2 arccot(π)`; Sullivan's atom `T₊ - T₋ = (-2, 0)/√(1+π²)` has norm
  `2/√(1+π²) = 2 sin(ϑ_E/2)` (Eq. 38), which differs from `ϑ_E`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

namespace EulerianCert.Corner

noncomputable def rE (θ : ℝ) : ℝ := 2 * Real.sin (θ / 2) / θ
noncomputable def rE' (θ : ℝ) : ℝ := Real.cos (θ / 2) / θ - 2 * Real.sin (θ / 2) / θ ^ 2
noncomputable def rE'' (θ : ℝ) : ℝ :=
  -Real.sin (θ / 2) / (2 * θ) - 2 * Real.cos (θ / 2) / θ ^ 2 + 4 * Real.sin (θ / 2) / θ ^ 3

lemma hasDerivAt_sin_half (θ : ℝ) :
    HasDerivAt (fun t => Real.sin (t / 2)) (Real.cos (θ / 2) / 2) θ := by
  have := ((hasDerivAt_id' θ).div_const 2).sin
  convert this using 1; ring

lemma hasDerivAt_cos_half (θ : ℝ) :
    HasDerivAt (fun t => Real.cos (t / 2)) (-Real.sin (θ / 2) / 2) θ := by
  have := ((hasDerivAt_id' θ).div_const 2).cos
  convert this using 1; ring

/-- Proof of Prop. 3.6: `r_E' = (cos(θ/2) - (2/θ) sin(θ/2))/θ`. -/
theorem hasDerivAt_rE {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt rE (rE' θ) θ := by
  have h := ((hasDerivAt_sin_half θ).const_mul 2).div (hasDerivAt_id' θ) hθ
  unfold rE rE'
  convert h using 1
  field_simp

theorem hasDerivAt_rE' {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt rE' (rE'' θ) θ := by
  have h1 := (hasDerivAt_cos_half θ).div (hasDerivAt_id θ) hθ
  have h2 := ((hasDerivAt_sin_half θ).const_mul 2).div ((hasDerivAt_id θ).pow 2)
    (pow_ne_zero 2 hθ)
  have h := h1.sub h2
  unfold rE' rE''
  convert h using 1
  · ext t; simp
  · simp; field_simp; ring

theorem rE_pi : rE π = 2 / π := by
  unfold rE; rw [Real.sin_pi_div_two]; ring

/-- Eq. (31): `r_E'(π) = -2/π²`. -/
theorem rE'_pi : rE' π = -2 / π ^ 2 := by
  unfold rE'
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- Eq. (40): the curvature numerator identity. -/
theorem curvature_numerator {θ : ℝ} (hθ : θ ≠ 0) :
    rE θ ^ 2 + 2 * rE' θ ^ 2 - rE θ * rE'' θ =
      (3 * θ * Real.sin (θ / 2) ^ 2 + 2 * (θ - Real.sin θ)) / θ ^ 3 := by
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hp := Real.sin_sq_add_cos_sq (θ / 2)
  unfold rE rE' rE''
  rw [hs]
  have key : ∀ s co : ℝ, s ^ 2 + co ^ 2 = 1 →
      (2 * s / θ) ^ 2 + 2 * (co / θ - 2 * s / θ ^ 2) ^ 2 -
        2 * s / θ * (-s / (2 * θ) - 2 * co / θ ^ 2 + 4 * s / θ ^ 3)
        = (3 * θ * s ^ 2 + 2 * (θ - 2 * s * co)) / θ ^ 3 := by
    intro s co h
    have e : (2 * s / θ) ^ 2 + 2 * (co / θ - 2 * s / θ ^ 2) ^ 2 -
        2 * s / θ * (-s / (2 * θ) - 2 * co / θ ^ 2 + 4 * s / θ ^ 3)
        - (3 * θ * s ^ 2 + 2 * (θ - 2 * s * co)) / θ ^ 3 = 2 * (co ^ 2 + s ^ 2 - 1) / θ ^ 2 := by
      field_simp; ring
    have : co ^ 2 + s ^ 2 - 1 = 0 := by linarith
    rw [this, mul_zero, zero_div] at e
    linarith [e]
  exact key _ _ hp

/-- Positivity of the numerator on `(0, π]` (indeed on `(0, ∞)`): signed curvature `> 0`. -/
theorem curvature_numerator_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < rE θ ^ 2 + 2 * rE' θ ^ 2 - rE θ * rE'' θ := by
  rw [curvature_numerator hθ.ne']
  have h1 : Real.sin θ < θ := Real.sin_lt hθ
  have h2 : 0 ≤ 3 * θ * Real.sin (θ / 2) ^ 2 := by positivity
  positivity

/-! ### The corner at `θ = ±π` -/

/-- Velocity of the polar curve `γ(θ) = r(θ)(cos θ, sin θ)`. -/
noncomputable def polarVel (r r' θ : ℝ) : ℝ × ℝ :=
  (r' * Real.cos θ - r * Real.sin θ, r' * Real.sin θ + r * Real.cos θ)

/-- Eq. (32), incoming tangent at `θ = π⁻`. -/
theorem tangent_minus : polarVel (rE π) (rE' π) π = (2 / π ^ 2, -(2 / π)) := by
  unfold polarVel; rw [rE_pi, rE'_pi, Real.cos_pi, Real.sin_pi]; ext <;> simp; ring

/-- Eq. (32), outgoing tangent at `θ = -π⁺` (by evenness `r_E'(-π⁺) = +2/π²`). -/
theorem tangent_plus : polarVel (rE π) (-rE' π) (-π) = (-(2 / π ^ 2), -(2 / π)) := by
  unfold polarVel
  rw [rE_pi, rE'_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  ext
  · simp; ring
  · simp

/-- Half-angle of the corner: each tangent deviates from the downward vertical by
`arctan((2/π²)/(2/π)) = arctan(1/π)`. -/
theorem half_angle_ratio : (2 / π ^ 2) / (2 / π) = 1 / π := by
  have := Real.pi_pos.ne'; field_simp

noncomputable def varthetaE : ℝ := 2 * Real.arctan (1 / π)

theorem tan_half_varthetaE : Real.tan (varthetaE / 2) = 1 / π := by
  unfold varthetaE; rw [mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan]

/-- `arctan(1/π) = arccot(π) = π/2 - arctan π`. -/
theorem arctan_inv_pi : Real.arctan (1 / π) = π / 2 - Real.arctan π := by
  rw [one_div, Real.arctan_inv_of_pos Real.pi_pos]

/-- Eq. (38): Sullivan's vector atom `T₊ - T₋` and its norm `2 sin(ϑ_E/2)`. -/
theorem sullivan_atom :
    let s := Real.sqrt (1 + π ^ 2)
    let Tm : ℝ × ℝ := (1 / s, -π / s)
    let Tp : ℝ × ℝ := (-1 / s, -π / s)
    Tp - Tm = (-2 / s, 0) ∧ 2 / s = 2 * Real.sin (varthetaE / 2) := by
  intro s Tm Tp
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  refine ⟨Prod.ext (by simp [Tm, Tp]; ring) (by simp [Tm, Tp]), ?_⟩
  unfold varthetaE
  rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sin_arctan]
  have hπ := Real.pi_pos
  have : Real.sqrt (1 + (1 / π) ^ 2) = s / π := by
    rw [show (1 : ℝ) + (1 / π) ^ 2 = (1 + π ^ 2) / π ^ 2 by field_simp; ring]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hπ.le]
  rw [this]
  field_simp

/-- The unit tangents of Eq. (36) are the normalised one-sided velocities. -/
theorem unit_tangents :
    let s := Real.sqrt (1 + π ^ 2)
    (2 / π ^ 2) / ((2 / π ^ 2) * s) = 1 / s ∧ (-(2 / π)) / ((2 / π ^ 2) * s) = -π / s := by
  intro s
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hπ := Real.pi_pos
  constructor <;> field_simp

/-- `‖(2/π², -2/π)‖ = (2/π²)√(1+π²)`. -/
theorem speed_at_corner :
    Real.sqrt ((2 / π ^ 2) ^ 2 + (2 / π) ^ 2) = (2 / π ^ 2) * Real.sqrt (1 + π ^ 2) := by
  have hπ := Real.pi_pos
  rw [show (2 / π ^ 2) ^ 2 + (2 / π) ^ 2 = (2 / π ^ 2) ^ 2 * (1 + π ^ 2) by field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end EulerianCert.Corner
