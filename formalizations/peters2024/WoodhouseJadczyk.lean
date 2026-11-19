import Peters2024
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Ring

/-! Explicit bridge from the linear direction of Woodhouse's alpha-plane
(1992, §2) to the normalized null cone of Jadczyk (2026, §8.3.2, Prop. 12).
The normalized null cone models positive rays (the oriented double cover).
We prove the representative-level geometry, not a physical wormhole or a
Lorentzian geodesic equation. -/
namespace Peters2024.WoodhouseJadczyk
noncomputable section

abbrev Ambient := ℂ × ℂ × ℂ

/-- Coordinate order: (x₁+ix₂, x₃+ix₅, x₄+ix₆). -/
def quad (X : Ambient) : ℝ := ‖X.1‖^2 + ‖X.2.1‖^2 - ‖X.2.2‖^2

def splitQuad (p : ℂ × ℂ) : ℝ := ‖p.1‖^2 - ‖p.2‖^2

def embed (p : ℂ × ℂ) : Ambient := (p.1, 0, p.2)

theorem embed_preserves_quad (p : ℂ × ℂ) : quad (embed p) = splitQuad p := by
  simp [quad, embed, splitQuad]

theorem embed_injective : Function.Injective embed := by
  intro p q h
  exact Prod.ext (congrArg (fun X : Ambient => X.1) h) (congrArg (fun X : Ambient => X.2.2) h)

/-- The image of the direction of the Woodhouse alpha-plane of orientation z. -/
def alpha (z : ℂ) : ℂ →ₗ[ℝ] Ambient where
  toFun u := (-(star z) * u, 0, u)
  map_add' u v := by simp [mul_add]
  map_smul' r u := by
    simp [Algebra.smul_def, mul_left_comm]

theorem alpha_injective (z : ℂ) : Function.Injective (alpha z) := by
  intro u v h
  exact congrArg (fun X : Ambient => X.2.2) h

theorem alpha_dimension (z : ℂ) : Module.finrank ℝ (LinearMap.range (alpha z)) = 2 := by
  rw [← (LinearEquiv.ofInjective (alpha z) (alpha_injective z)).finrank_eq,
    Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]

theorem alpha_null (z u : ℂ) (hz : ‖z‖ = 1) : quad (alpha z u) = 0 := by
  change ‖-(star z) * u‖^2 + ‖(0 : ℂ)‖^2 - ‖u‖^2 = 0
  rw [norm_mul, norm_neg]
  change (‖(starRingEnd ℂ) z‖ * ‖u‖)^2 + ‖(0 : ℂ)‖^2 - ‖u‖^2 = 0
  simp [hz]

theorem alpha_range_totally_null (z : ℂ) (hz : ‖z‖ = 1) :
    ∀ X ∈ LinearMap.range (alpha z), quad X = 0 := by
  rintro X ⟨u, rfl⟩
  exact alpha_null z u hz

/-- A normalized positive-ray representative in the null cone. -/
def normalized (X : Ambient) : Prop :=
  ‖X.1‖^2 + ‖X.2.1‖^2 = 1 ∧ ‖X.2.2‖ = 1

abbrev DoubleCover := {X : Ambient // normalized X}

def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

theorem phase_antipodal (t : ℝ) : phase (t + Real.pi) = -phase t := by
  unfold phase
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem phase_periodic (t : ℝ) : phase (t + 2 * Real.pi) = phase t := by
  rw [two_mul, ← add_assoc, phase_antipodal, phase_antipodal, neg_neg]

def curve (z : ℂ) (t : ℝ) : Ambient := alpha z (phase t)

theorem curve_continuous (z : ℂ) : Continuous (curve z) := by
  have h : Continuous phase := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  change Continuous (fun t => (-(star z) * phase t, (0 : ℂ), phase t))
  exact (continuous_const.mul h).prodMk (continuous_const.prodMk h)

theorem curve_normalized (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) : normalized (curve z t) := by
  unfold normalized
  change ‖-(star z) * phase t‖^2 + ‖(0 : ℂ)‖^2 = 1 ∧ ‖phase t‖ = 1
  rw [norm_mul, norm_neg, phase_norm]
  change (‖(starRingEnd ℂ) z‖ * 1)^2 + ‖(0 : ℂ)‖^2 = 1 ∧ (1 : ℝ) = 1
  simp [hz]

theorem curve_null (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) : quad (curve z t) = 0 :=
  alpha_null z (phase t) hz

theorem curve_antipodal (z : ℂ) (t : ℝ) : curve z (t + Real.pi) = -curve z t := by
  simp [curve, phase_antipodal]

theorem curve_periodic (z : ℂ) : Function.Periodic (curve z) (2 * Real.pi) := by
  intro t
  simp [curve, phase_periodic]

/-- x₅ − x₆ distinguishes the two affine Minkowski charts in the positive-ray
cover; zero is their common conformal infinity (Jadczyk, §§7, 8.3.2). -/
def chartSign (X : Ambient) : ℝ := X.2.1.im - X.2.2.im

theorem curve_chartSign (z : ℂ) (t : ℝ) : chartSign (curve z t) = -Real.sin t := by
  change (0 : ℂ).im - (Complex.exp ((t : ℂ) * Complex.I)).im = _
  simp [Complex.exp_im]

theorem curve_negative_chart (z : ℂ) {t : ℝ} (h₀ : 0 < t) (hπ : t < Real.pi) :
    chartSign (curve z t) < 0 := by
  rw [curve_chartSign]
  exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi h₀ hπ)

theorem curve_positive_chart (z : ℂ) {t : ℝ} (h₀ : -Real.pi < t) (hπ : t < 0) :
    0 < chartSign (curve z t) := by
  rw [curve_chartSign]
  exact neg_pos.mpr (Real.sin_neg_of_neg_of_neg_pi_lt hπ h₀)

theorem curve_infinity (z : ℂ) : chartSign (curve z 0) = 0 ∧ chartSign (curve z Real.pi) = 0 := by
  simp [curve_chartSign]

def orientedCurve (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) : DoubleCover :=
  ⟨curve z t, curve_normalized z hz t⟩

theorem orientedCurve_continuous (z : ℂ) (hz : ‖z‖ = 1) : Continuous (orientedCurve z hz) :=
  (curve_continuous z).subtype_mk _

/-- A single continuous curve in the normalized null cone meets both charts,
and crosses their common infinity. No physical transport is asserted. -/
theorem oriented_crossing (z : ℂ) (hz : ‖z‖ = 1) :
    (∃ t : ℝ, 0 < chartSign (orientedCurve z hz t).val) ∧
    (∃ t : ℝ, chartSign (orientedCurve z hz t).val = 0) ∧
    (∃ t : ℝ, chartSign (orientedCurve z hz t).val < 0) := by
  refine ⟨⟨-Real.pi / 2, ?_⟩, ⟨0, (curve_infinity z).1⟩, ⟨Real.pi / 2, ?_⟩⟩
  · exact curve_positive_chart z (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  · exact curve_negative_chart z (by positivity) (by linarith [Real.pi_pos])

/-- The normalized cone is exactly one representative per positive null ray:
every nonzero null vector has a positive multiple in it. -/
theorem normalized_ray_exists (X : Ambient) (hX : X ≠ 0) (hq : quad X = 0) :
    ∃ r : ℝ, 0 < r ∧ normalized (r • X) := by
  have ht : 0 < ‖X.2.2‖ := by
    by_contra! hn
    have hzero : ‖X.2.2‖ = 0 := le_antisymm hn (norm_nonneg _)
    have hsum : ‖X.1‖^2 + ‖X.2.1‖^2 = 0 := by simpa [quad, hzero] using hq
    have h₁ : ‖X.1‖ = 0 := by nlinarith [sq_nonneg ‖X.2.1‖]
    have h₂ : ‖X.2.1‖ = 0 := by nlinarith [sq_nonneg ‖X.1‖]
    apply hX
    exact Prod.ext (norm_eq_zero.mp h₁) (Prod.ext (norm_eq_zero.mp h₂) (norm_eq_zero.mp hzero))
  refine ⟨‖X.2.2‖⁻¹, inv_pos.mpr ht, ?_⟩
  have hsum : ‖X.1‖^2 + ‖X.2.1‖^2 = ‖X.2.2‖^2 := by
    unfold quad at hq
    linarith
  change ‖‖X.2.2‖⁻¹ • X.1‖^2 + ‖‖X.2.2‖⁻¹ • X.2.1‖^2 = 1 ∧ ‖‖X.2.2‖⁻¹ • X.2.2‖ = 1
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_cancel₀ ht.ne']
  constructor
  · rw [mul_pow, mul_pow, ← mul_add, hsum, ← mul_pow, inv_mul_cancel₀ ht.ne']
    norm_num
  · trivial

theorem normalized_ray_unique {X : Ambient} {r : ℝ} (hX : normalized X) (hr : 0 < r)
    (h : normalized (r • X)) : r = 1 := by
  have ht := hX.2
  have hs := h.2
  change ‖r • X.2.2‖ = 1 at hs
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hr, ht, mul_one] at hs

/-- Unlike the unoriented projectivization, normalized antipodes are distinct. -/
theorem normalized_antipodes_distinct {X : Ambient} (hX : normalized X) : X ≠ -X := by
  intro h
  have he : X.2.2 = -X.2.2 := congrArg (fun X : Ambient => X.2.2) h
  have hz : X.2.2 = 0 := by linear_combination he / 2
  simpa [hz] using hX.2

/-- The two infinity intersections at t=0 and t=π are distinct in the double cover. -/
theorem infinity_antipodes_distinct (z : ℂ) (hz : ‖z‖ = 1) : curve z 0 ≠ curve z Real.pi := by
  rw [← zero_add Real.pi, curve_antipodal]
  exact normalized_antipodes_distinct (curve_normalized z hz 0)

theorem normalized_nonzero_null {X : Ambient} (h : normalized X) : X ≠ 0 ∧ quad X = 0 := by
  constructor
  · intro he
    rw [he] at h
    simp [normalized] at h
  · unfold quad
    rw [h.1, h.2]
    norm_num

/-- Normalizing by the signed affine coordinate erases the distinction between
antipodal lifts. This is not true of normalization by a positive scale. -/
def affineRepresentative (X : Ambient) : Ambient := (chartSign X)⁻¹ • X

theorem chartSign_neg (X : Ambient) : chartSign (-X) = -chartSign X := by
  simp [chartSign]
  ring

theorem affineRepresentative_antipodal (X : Ambient) :
    affineRepresentative (-X) = affineRepresentative X := by
  rw [affineRepresentative, chartSign_neg, inv_neg, neg_smul, smul_neg, neg_neg]
  rfl

/-- The antipodal half-turn takes a point in one chart to the other chart,
without changing its unoriented affine representative. -/
theorem half_turn_switches_chart (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ)
    (ht : chartSign (curve z t) ≠ 0) :
    curve z (t + Real.pi) ≠ curve z t ∧
    chartSign (curve z (t + Real.pi)) = -chartSign (curve z t) ∧
    chartSign (curve z (t + Real.pi)) * chartSign (curve z t) < 0 ∧
    affineRepresentative (curve z (t + Real.pi)) = affineRepresentative (curve z t) := by
  rw [curve_antipodal]
  refine ⟨(normalized_antipodes_distinct (curve_normalized z hz t)).symm,
    chartSign_neg _, ?_, affineRepresentative_antipodal _⟩
  rw [chartSign_neg, neg_mul]
  exact neg_neg_of_pos (mul_self_pos.mpr ht)

end
end Peters2024.WoodhouseJadczyk

#print axioms Peters2024.WoodhouseJadczyk.embed_preserves_quad
#print axioms Peters2024.WoodhouseJadczyk.embed_injective
#print axioms Peters2024.WoodhouseJadczyk.alpha_injective
#print axioms Peters2024.WoodhouseJadczyk.alpha_dimension
#print axioms Peters2024.WoodhouseJadczyk.alpha_null
#print axioms Peters2024.WoodhouseJadczyk.alpha_range_totally_null
#print axioms Peters2024.WoodhouseJadczyk.phase_norm
#print axioms Peters2024.WoodhouseJadczyk.phase_antipodal
#print axioms Peters2024.WoodhouseJadczyk.phase_periodic
#print axioms Peters2024.WoodhouseJadczyk.curve_continuous
#print axioms Peters2024.WoodhouseJadczyk.curve_normalized
#print axioms Peters2024.WoodhouseJadczyk.curve_null
#print axioms Peters2024.WoodhouseJadczyk.curve_antipodal
#print axioms Peters2024.WoodhouseJadczyk.curve_periodic
#print axioms Peters2024.WoodhouseJadczyk.curve_chartSign
#print axioms Peters2024.WoodhouseJadczyk.curve_negative_chart
#print axioms Peters2024.WoodhouseJadczyk.curve_positive_chart
#print axioms Peters2024.WoodhouseJadczyk.curve_infinity
#print axioms Peters2024.WoodhouseJadczyk.orientedCurve_continuous
#print axioms Peters2024.WoodhouseJadczyk.oriented_crossing
#print axioms Peters2024.WoodhouseJadczyk.normalized_ray_exists
#print axioms Peters2024.WoodhouseJadczyk.normalized_ray_unique
#print axioms Peters2024.WoodhouseJadczyk.normalized_antipodes_distinct
#print axioms Peters2024.WoodhouseJadczyk.infinity_antipodes_distinct
#print axioms Peters2024.WoodhouseJadczyk.normalized_nonzero_null
#print axioms Peters2024.WoodhouseJadczyk.chartSign_neg
#print axioms Peters2024.WoodhouseJadczyk.affineRepresentative_antipodal
#print axioms Peters2024.WoodhouseJadczyk.half_turn_switches_chart
