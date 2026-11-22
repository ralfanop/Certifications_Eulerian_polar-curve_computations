import PrivateApex.CardioidIdentities
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
PRIVATE.  Manuscript 15, Section 7.10: modular inversion and conformal homothety of the
cardioid.

* `z1`, `z1_eq_two_mul_z0`, `z0_mul_z1`, `z1_eq_neg_inv_z0`, `z0_eq_neg_inv_z1`, `z1_sq`,
  `z0_add_z1`, `special_quadratic`: the distinguished pair `(z0, z1) = (i/√2, i√2)`;
* `quadratic_family_product`, `quadratic_family_involution`, `quadratic_family_factor`,
  `golden_quadratic`, `golden_other_root`, `special_quadratic_family`: the roots of
  `w^2 - a w - 1` have product `-1` and are exchanged by `w ↦ -1/w`; `a = 1` gives `φ` and
  `-1/φ`, `a = 3i/√2` gives `z0` and `z1`;
* `z0H`, `z1H`, `S_smul_z0H`, `S_smul_z1H`, `modular_invariant_eq`: both points lie in the upper
  half-plane, the modular inversion `S` exchanges them, so every `SL(2, ℤ)`-invariant function
  (the modular invariant `j` among them) takes the same value at both;
* `cardioidFam`, `cardioidFam_z0`, `cardioidFam_z1`, `cardioidFam_eulerian`,
  `cardioid_homothety`: the two parametrised cardioids, their Eulerian representation and the
  homothety of ratio `4` about the cusp;
* `norm_cardioidFam_z0`, `norm_cardioidFam_z1`, `cardioidFam_pi`, `cardioidFam_pi_z0`,
  `cardioidFam_pi_z1`, `cardioidFam_half_pi_z0`, `cardioidFam_half_pi_z1`: distances from the
  cusp and the special values at `θ = π` and `θ = π/2`;
* `H4`, `H4_eq`, `H4_cusp`, `H4_cardioid`, `hasDerivAt_H4`, `H4_dist`, `H4_dist_sq`,
  `H4_pullback`: the cusp-centred homothety, its derivative `4`, the distance scaling `4` and
  the scaling `16` of the Euclidean metric;
* `sphDensity`, `H4_spherical_dilation_cusp`, `H4inf`, `H4inf_eq`, `hasDerivAt_H4inf`,
  `H4_spherical_dilation_infinity`, `H4_spherical_dilation_formula`: the round spherical
  dilation of the Möbius extension is `4` at the cusp and `1/4` at infinity;
* `H4_not_modular`: `H4` is not the action of any element of `SL(2, ℤ)` on the upper half-plane.
-/

namespace PrivateApex
namespace Cardioid
open Complex
open scoped Real MatrixGroups

/-! ### The distinguished pair -/

/-- The second distinguished point `z1 = i √2`. -/
noncomputable def z1 : ℂ := I * (Real.sqrt 2 : ℂ)

theorem sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast this.ne'

theorem sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem z1_eq_two_mul_z0 : z1 = 2 * z0 := by
  unfold z1 z0
  rw [show (2 : ℂ) * (I / (Real.sqrt 2 : ℂ)) = 2 * I / (Real.sqrt 2 : ℂ) by ring,
    eq_div_iff sqrt2_ne_zero]
  linear_combination I * sqrt2_sq

theorem z0_mul_z1 : z0 * z1 = -1 := by
  unfold z0 z1
  rw [show I / (Real.sqrt 2 : ℂ) * (I * (Real.sqrt 2 : ℂ)) =
      I * I * ((Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ)) by ring,
    div_self sqrt2_ne_zero, mul_one, I_mul_I]

theorem z0_ne_zero : z0 ≠ 0 := by
  intro h
  have := z0_mul_z1
  rw [h, zero_mul] at this
  norm_num at this

theorem z1_ne_zero : z1 ≠ 0 := by
  intro h
  have := z0_mul_z1
  rw [h, mul_zero] at this
  norm_num at this

theorem z1_eq_neg_inv_z0 : z1 = -1 / z0 := by
  rw [eq_div_iff z0_ne_zero, mul_comm, z0_mul_z1]

theorem z0_eq_neg_inv_z1 : z0 = -1 / z1 := by
  rw [eq_div_iff z1_ne_zero, z0_mul_z1]

theorem z1_sq : z1 ^ 2 = -2 := by
  rw [z1_eq_two_mul_z0, mul_pow, z0_sq]
  norm_num

theorem z0_add_z1 : z0 + z1 = 3 * I / (Real.sqrt 2 : ℂ) := by
  unfold z0 z1
  rw [eq_div_iff sqrt2_ne_zero, add_mul, div_mul_cancel₀ _ sqrt2_ne_zero]
  linear_combination I * sqrt2_sq

/-- `(w - z0)(w - z1) = w^2 - (3i/√2) w - 1`. -/
theorem special_quadratic (w : ℂ) :
    (w - z0) * (w - z1) = w ^ 2 - 3 * I / (Real.sqrt 2 : ℂ) * w - 1 := by
  have h1 := z0_add_z1
  have h2 := z0_mul_z1
  linear_combination (-w) * h1 + h2

/-! ### The quadratic family `w^2 - a w - 1` -/

/-- The two roots of `w^2 - a w - 1` have product `-1`. -/
theorem quadratic_family_product {a r s : ℂ}
    (h : ∀ w : ℂ, w ^ 2 - a * w - 1 = (w - r) * (w - s)) : r * s = -1 := by
  have h0 := h 0
  linear_combination -h0

/-- A root of `w^2 - a w - 1` is nonzero, and `w ↦ -1/w` maps it to a root. -/
theorem quadratic_family_involution {a r : ℂ} (hr : r ^ 2 - a * r - 1 = 0) :
    r ≠ 0 ∧ (-1 / r) ^ 2 - a * (-1 / r) - 1 = 0 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr
  refine ⟨hr0, ?_⟩
  field_simp
  linear_combination -hr

/-- Factorisation through a root: `w^2 - a w - 1 = (w - r)(w - (-1/r))`. -/
theorem quadratic_family_factor {a r : ℂ} (hr : r ^ 2 - a * r - 1 = 0) (w : ℂ) :
    w ^ 2 - a * w - 1 = (w - r) * (w - (-1 / r)) := by
  have hr0 := (quadratic_family_involution hr).1
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  rw [neg_div, one_div]
  linear_combination (w * r⁻¹) * hr + (1 - w * r + a * w) * hinv

open Real in
/-- For `a = 1` the roots are the golden ratio `φ` and `-1/φ`. -/
theorem golden_quadratic (w : ℂ) :
    w ^ 2 - 1 * w - 1 = (w - (goldenRatio : ℂ)) * (w - (-1 / (goldenRatio : ℂ))) := by
  apply quadratic_family_factor
  have h := goldenRatio_sq
  have h' : ((goldenRatio : ℝ) : ℂ) ^ 2 = (goldenRatio : ℂ) + 1 := by exact_mod_cast h
  linear_combination h'

open Real in
/-- The second root `-1/φ` is the conjugate `ψ = (1 - √5)/2`. -/
theorem golden_other_root : -1 / goldenRatio = goldenConj := by
  rw [neg_div, one_div, inv_goldenRatio, neg_neg]

/-- For `a = 3i/√2` the roots are `z0` and `z1`. -/
theorem special_quadratic_family (w : ℂ) :
    w ^ 2 - 3 * I / (Real.sqrt 2 : ℂ) * w - 1 = (w - z0) * (w - (-1 / z0)) := by
  rw [← z1_eq_neg_inv_z0, special_quadratic]

/-! ### The modular inversion on the upper half-plane -/

theorem z0_im_pos : 0 < z0.im := by
  unfold z0
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_ofReal_im, I_im]
  positivity

theorem z1_im_pos : 0 < z1.im := by
  unfold z1
  simp

/-- `z0` as a point of the upper half-plane. -/
noncomputable def z0H : UpperHalfPlane := UpperHalfPlane.mk z0 z0_im_pos

/-- `z1` as a point of the upper half-plane. -/
noncomputable def z1H : UpperHalfPlane := UpperHalfPlane.mk z1 z1_im_pos

/-- The modular inversion `S : τ ↦ -1/τ` maps `z0` to `z1`. -/
theorem S_smul_z0H : ModularGroup.S • z0H = z1H := by
  rw [UpperHalfPlane.modular_S_smul]
  ext
  simp only [UpperHalfPlane.coe_mk, z0H, z1H]
  rw [z1_eq_neg_inv_z0, inv_neg, neg_div, one_div]

/-- The modular inversion `S` maps `z1` to `z0`. -/
theorem S_smul_z1H : ModularGroup.S • z1H = z0H := by
  rw [UpperHalfPlane.modular_S_smul]
  ext
  simp only [UpperHalfPlane.coe_mk, z0H, z1H]
  rw [z0_eq_neg_inv_z1, inv_neg, neg_div, one_div]

/-- Any function on the upper half-plane invariant under `SL(2, ℤ)` (for instance the modular
invariant `j`, by its classical invariance) takes the same value at `z0` and `z1`. -/
theorem modular_invariant_eq {β : Type*} (f : UpperHalfPlane → β)
    (hf : ∀ (g : SL(2, ℤ)) (τ : UpperHalfPlane), f (g • τ) = f τ) : f z0H = f z1H := by
  rw [← S_smul_z0H, hf]

/-! ### The two cardioids -/

/-- The cardioid attached to `z`: `c(θ) = 1/4 + (z^2/2)(e^{iθ} - 1)^2`. -/
noncomputable def cardioidFam (z : ℂ) (θ : ℝ) : ℂ :=
  1 / 4 + z ^ 2 / 2 * (exp ((θ : ℂ) * I) - 1) ^ 2

/-- For `z = z0` this is the main cardioid. -/
theorem cardioidFam_z0 (θ : ℝ) : cardioidFam z0 θ = cardioid θ := by
  have h := cardioid_special_point θ
  unfold cardioidFam
  linear_combination -h

/-- For `z = z1`: `c₁(θ) = 1/4 - (e^{iθ} - 1)^2`. -/
theorem cardioidFam_z1 (θ : ℝ) : cardioidFam z1 θ = 1 / 4 - (exp ((θ : ℂ) * I) - 1) ^ 2 := by
  unfold cardioidFam
  rw [z1_sq]
  ring

/-- Eulerian representation: `c(θ) - 1/4 = -(z^2/2) e^{iθ} θ^2 r_E(θ)^2`, for every real `θ`. -/
theorem cardioidFam_eulerian (z : ℂ) (θ : ℝ) :
    cardioidFam z θ - 1 / 4 =
      -(z ^ 2 / 2) * exp ((θ : ℂ) * I) * (θ : ℂ) ^ 2 * (rE θ : ℂ) ^ 2 := by
  unfold cardioidFam
  rw [exp_sub_one_sq]
  ring

/-- The homothety of ratio `4` about the cusp. -/
theorem cardioid_homothety (θ : ℝ) :
    cardioidFam z1 θ - 1 / 4 = 4 * (cardioidFam z0 θ - 1 / 4) := by
  unfold cardioidFam
  rw [z1_sq, z0_sq]
  ring

theorem norm_cardioidFam_z0 (θ : ℝ) :
    ‖cardioidFam z0 θ - 1 / 4‖ = Real.sin (θ / 2) ^ 2 := by
  rw [cardioidFam_z0, cardioid_polar, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_cardioidFam_z1 (θ : ℝ) :
    ‖cardioidFam z1 θ - 1 / 4‖ = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [cardioid_homothety, norm_mul, norm_cardioidFam_z0]
  norm_num

/-- At `θ = π`, with `r_E(π) = 2/π`: `c(π) - 1/4 = 2 z^2`. -/
theorem cardioidFam_pi (z : ℂ) : cardioidFam z π - 1 / 4 = 2 * z ^ 2 := by
  rw [cardioidFam_eulerian, rE_pi, Complex.exp_pi_mul_I]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem cardioidFam_pi_z0 : cardioidFam z0 π = -3 / 4 := by
  have h := cardioidFam_pi z0
  rw [z0_sq] at h
  linear_combination h

theorem cardioidFam_pi_z1 : cardioidFam z1 π = -15 / 4 := by
  have h := cardioidFam_pi z1
  rw [z1_sq] at h
  linear_combination h

theorem exp_half_pi_I : exp (((π / 2 : ℝ) : ℂ) * I) = I := by
  rw [show ((π / 2 : ℝ) : ℂ) * I = ((π / 2 : ℝ) : ℂ) * I + 0 by ring, Complex.exp_add,
    Complex.exp_zero, mul_one, Complex.exp_mul_I]
  push_cast
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem cardioidFam_half_pi_z0 : cardioidFam z0 (π / 2) = 1 / 4 + I / 2 := by
  unfold cardioidFam
  rw [exp_half_pi_I, z0_sq]
  linear_combination (-1 / 4 : ℂ) * I_sq

theorem cardioidFam_half_pi_z1 : cardioidFam z1 (π / 2) = 1 / 4 + 2 * I := by
  unfold cardioidFam
  rw [exp_half_pi_I, z1_sq]
  linear_combination (-1 : ℂ) * I_sq

/-- At `θ = π/2` both points lie on the vertical ray from the cusp, at distances `1/2` and `2`. -/
theorem half_pi_ray :
    (cardioidFam z0 (π / 2)).re = 1 / 4 ∧ (cardioidFam z1 (π / 2)).re = 1 / 4 ∧
      ‖cardioidFam z0 (π / 2) - 1 / 4‖ = 1 / 2 ∧ ‖cardioidFam z1 (π / 2) - 1 / 4‖ = 2 := by
  rw [cardioidFam_half_pi_z0, cardioidFam_half_pi_z1]
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [show (1 / 4 + I / 2 - 1 / 4 : ℂ) = I / 2 by ring, norm_div, Complex.norm_I]
    norm_num
  · rw [show (1 / 4 + 2 * I - 1 / 4 : ℂ) = 2 * I by ring, norm_mul, Complex.norm_I]
    norm_num

/-! ### The cusp-centred homothety `H4` -/

/-- `H4(c) = 4c - 3/4`. -/
noncomputable def H4 (c : ℂ) : ℂ := 4 * c - 3 / 4

theorem H4_eq (c : ℂ) : H4 c = 1 / 4 + 4 * (c - 1 / 4) := by
  unfold H4
  ring

theorem H4_cusp : H4 (1 / 4) = 1 / 4 := by
  unfold H4
  norm_num

/-- `H4` maps the main cardioid onto the second one, parameter by parameter. -/
theorem H4_cardioid (θ : ℝ) : H4 (cardioidFam z0 θ) = cardioidFam z1 θ := by
  have h := cardioid_homothety θ
  rw [H4_eq]
  linear_combination -h

theorem hasDerivAt_H4 (c : ℂ) : HasDerivAt H4 4 c := by
  have h := ((hasDerivAt_id' c).const_mul (4 : ℂ)).sub_const (3 / 4 : ℂ)
  rw [mul_one] at h
  exact h

theorem H4_dist (a b : ℂ) : ‖H4 a - H4 b‖ = 4 * ‖a - b‖ := by
  rw [show H4 a - H4 b = 4 * (a - b) by unfold H4; ring, norm_mul]
  norm_num

/-- The Euclidean metric is multiplied by `16`. -/
theorem H4_dist_sq (a b : ℂ) : ‖H4 a - H4 b‖ ^ 2 = 16 * ‖a - b‖ ^ 2 := by
  rw [H4_dist]
  ring

/-- Pullback of the Euclidean metric along a curve: velocities are multiplied by `4`, squared
lengths by `16`. -/
theorem H4_pullback {γ : ℝ → ℂ} {v : ℂ} {t : ℝ} (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => H4 (γ s)) (4 * v) t ∧ ‖4 * v‖ ^ 2 = 16 * ‖v‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact (hasDerivAt_H4 (γ t)).comp t hγ
  · rw [norm_mul]
    norm_num
    ring

/-! ### The spherical dilation of the Möbius extension -/

/-- Density of the round metric on the Riemann sphere, `2 |dz| / (1 + |z|^2)`. -/
noncomputable def sphDensity (z : ℂ) : ℝ := 2 / (1 + ‖z‖ ^ 2)

theorem sphDensity_pos (z : ℂ) : 0 < sphDensity z := by
  unfold sphDensity
  positivity

/-- Spherical dilation at a finite point: `|H4'(z)| ρ(H4 z) / ρ(z)`. -/
theorem H4_spherical_dilation_formula (z : ℂ) :
    ‖(4 : ℂ)‖ * sphDensity (H4 z) / sphDensity z = 4 * (1 + ‖z‖ ^ 2) / (1 + ‖H4 z‖ ^ 2) := by
  unfold sphDensity
  have h1 : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + ‖H4 z‖ ^ 2 := by positivity
  rw [show ‖(4 : ℂ)‖ = 4 by norm_num]
  field_simp

/-- At the fixed cusp the spherical dilation is `4`. -/
theorem H4_spherical_dilation_cusp :
    ‖(4 : ℂ)‖ * sphDensity (H4 (1 / 4)) / sphDensity (1 / 4) = 4 := by
  rw [H4_cusp, mul_div_assoc, div_self (sphDensity_pos _).ne']
  norm_num

/-- `H4` in the chart `w = 1/z` at infinity: `w ↦ w / (4 - 3w/4)`. -/
noncomputable def H4inf (w : ℂ) : ℂ := w / (4 - 3 / 4 * w)

theorem H4inf_eq {w : ℂ} (hw : w ≠ 0) (h : 4 - 3 / 4 * w ≠ 0) : H4inf w = 1 / H4 (1 / w) := by
  unfold H4inf H4
  have h' : 4 * (1 / w) - 3 / 4 ≠ 0 := by
    intro h0
    apply h
    field_simp at h0 ⊢
    linear_combination h0
  field_simp

theorem H4inf_zero : H4inf 0 = 0 := by simp [H4inf]

theorem hasDerivAt_H4inf : HasDerivAt H4inf (1 / 4) 0 := by
  have hden : HasDerivAt (fun w : ℂ => 4 - 3 / 4 * w) (-(3 / 4 * 1)) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).const_mul (3 / 4 : ℂ)).const_sub (4 : ℂ)
  have h := (hasDerivAt_id' (0 : ℂ)).div hden (by norm_num)
  exact h.congr_deriv (by norm_num)

/-- At infinity (the fixed point `w = 0` of the chart) the spherical dilation is `1/4`. -/
theorem H4_spherical_dilation_infinity :
    ‖(1 / 4 : ℂ)‖ * sphDensity (H4inf 0) / sphDensity 0 = 1 / 4 := by
  rw [H4inf_zero, mul_div_assoc, div_self (sphDensity_pos _).ne']
  norm_num

/-- The spherical dilation is not constant, so `H4` is not a similarity of the round metric. -/
theorem H4_spherical_not_constant :
    ‖(4 : ℂ)‖ * sphDensity (H4 (1 / 4)) / sphDensity (1 / 4) ≠
      ‖(1 / 4 : ℂ)‖ * sphDensity (H4inf 0) / sphDensity 0 := by
  rw [H4_spherical_dilation_cusp, H4_spherical_dilation_infinity]
  norm_num

/-! ### `H4` is not modular -/

/-- No element of `SL(2, ℤ)` acts on the upper half-plane as `τ ↦ 4τ - 3/4`. -/
theorem H4_not_modular :
    ¬ ∃ g : SL(2, ℤ), ∀ τ : UpperHalfPlane, ((g • τ : UpperHalfPlane) : ℂ) = H4 τ := by
  rintro ⟨g, hg⟩
  set A : ℝ := ((g 0 0 : ℤ) : ℝ) with hA
  set B : ℝ := ((g 0 1 : ℤ) : ℝ) with hB
  set C : ℝ := ((g 1 0 : ℤ) : ℝ) with hC
  set D : ℝ := ((g 1 1 : ℤ) : ℝ) with hD
  -- the identity at `τ = k i`, `k > 0`
  have key : ∀ k : ℝ, 0 < k →
      (A : ℂ) * (k * I) + B = (4 * (k * I) - 3 / 4) * ((C : ℂ) * (k * I) + D) := by
    intro k hk
    have him : 0 < ((k : ℂ) * I).im := by simpa using hk
    have h := hg (UpperHalfPlane.mk ((k : ℂ) * I) him)
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_mk] at h
    simp only [algebraMap_int_eq, eq_intCast] at h
    have hne : (C : ℂ) * (k * I) + D ≠ 0 := by
      intro h0
      rw [show ((g 1 0 : ℤ) : ℝ) = C from rfl, show ((g 1 1 : ℤ) : ℝ) = D from rfl] at h
      push_cast [← hC, ← hD] at h
      rw [h0, div_zero] at h
      have := congrArg Complex.im h
      simp [H4] at this
      linarith
    unfold H4 at h
    push_cast [← hA, ← hB, ← hC, ← hD] at h
    rw [div_eq_iff hne] at h
    exact h
  have e1 := key 1 one_pos
  have e2 := key 2 two_pos
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  have r2 := congrArg Complex.re e2
  simp at r1 i1 r2
  have hC0 : C = 0 := by nlinarith
  have hAD : A = 4 * D := by
    rw [hC0] at i1
    linarith
  have hc : g 1 0 = 0 := by
    rw [hC] at hC0
    exact_mod_cast hC0
  have ha : g 0 0 = 4 * g 1 1 := by
    rw [hA, hD] at hAD
    exact_mod_cast hAD
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  rw [ha, hc] at hdet
  have h4 : (4 : ℤ) ∣ 1 := ⟨g 1 1 * g 1 1, by linarith⟩
  norm_num at h4

end Cardioid
end PrivateApex
