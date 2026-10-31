/-
# Theorem 3.12 of the V001 manuscript: the unique radial uniform minimiser (existence part)

With `x = cos θ`, `f(x) = r_E(arccos x)`, `q = 2/π`, `c = (1+q)/2`, `m = (1−q)/2`, `ℓ(x) = c + m x`
(Eq. (58)):
* Eqs. (62)–(64): `f(x) = ∫₀¹ cos((t/2) arccos x) dt`; for `0 < α < 1`, `x ↦ cos(α arccos x)` has
  second derivative `−α G_α(θ)/sin³θ` with `G_α(θ) = α sin θ cos(αθ) − cos θ sin(αθ) > 0` (because
  `G_α(0) = 0`, `G_α' = (1 − α²) sin θ sin(αθ) > 0`); hence `f` is strictly concave on `[-1, 1]`.
* `f − ℓ` vanishes at `±1`, is strictly concave, and attains a unique positive maximum `Δ` at an
  interior point `x* = cos θ*`, characterised by `f'(x*) = m`, i.e. Eq. (59)
  `m = (2 sin(θ*/2) − θ* cos(θ*/2))/(θ*² sin θ*)`, with `θ* ∈ (0, π)` the unique solution there.
* Eqs. (60)–(61): `ℓ + Δ/2` has uniform error `ε_rad = Δ/2` on `[-1, 1]`; every affine `β + αx`
  has uniform error `≥ Δ/2`, with equality only for `α = m`, `β = c + Δ/2`; and
  `b_rad > 2 a_rad > 0`.
The decimals of Eqs. (59)–(61) are certified by interval arithmetic (README §2).
-/
import EulerianCert.FourierModes
import EulerianCert.Corner
import EulerianCert.Limacon
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Real Set intervalIntegral

noncomputable section

namespace EulerianCert.RadialMinimax

open EulerianCert.Limacon (q c m)

/-! ### `G_α > 0`, Eq. (64) -/

def G (α θ : ℝ) : ℝ := α * Real.sin θ * Real.cos (α * θ) - Real.cos θ * Real.sin (α * θ)

lemma hasDerivAt_G (α θ : ℝ) :
    HasDerivAt (G α) ((1 - α ^ 2) * Real.sin θ * Real.sin (α * θ)) θ := by
  have h1 := (Real.hasDerivAt_sin θ).const_mul α
  have h2 := ((hasDerivAt_id' θ).const_mul α).cos
  have h3 := ((hasDerivAt_id' θ).const_mul α).sin
  have h := (h1.mul h2).sub ((Real.hasDerivAt_cos θ).mul h3)
  unfold G
  convert h using 1
  ring

lemma G_pos {α θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθπ : θ < π) : 0 < G α θ := by
  have hmono : StrictMonoOn (G α) (Icc 0 π) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 π)
      (fun x _ => (hasDerivAt_G α x).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_G α x).deriv]
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hsa : 0 < Real.sin (α * x) := Real.sin_pos_of_pos_of_lt_pi (mul_pos hα0 hx.1)
      (by nlinarith [hx.2, hx.1])
    have : 0 < 1 - α ^ 2 := by nlinarith
    positivity
  have := hmono ⟨le_rfl, pi_pos.le⟩ ⟨hθ0.le, hθπ.le⟩ hθ0
  simpa [G] using this

/-! ### Strict concavity of `x ↦ cos(α arccos x)`, Eq. (63) -/

def φ (α x : ℝ) : ℝ := Real.cos (α * Real.arccos x)

def ψ (α x : ℝ) : ℝ := α * Real.sin (α * Real.arccos x) / √(1 - x ^ 2)

lemma sqrt_pos_of_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < √(1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_φ (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (φ α) (ψ α x) x := by
  have ha := hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have h := (ha.const_mul α).cos
  unfold φ ψ
  convert h using 1
  have hs := sqrt_pos_of_mem hx
  field_simp

lemma hasDerivAt_sqrt_one_sub {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => √(1 - y ^ 2)) (-x / √(1 - x ^ 2)) x := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have h := h1.sqrt hpos.ne'
  convert h using 1
  have hs := sqrt_pos_of_mem hx
  field_simp

lemma hasDerivAt_ψ (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (ψ α) (-α * G α (Real.arccos x) / √(1 - x ^ 2) ^ 3) x := by
  have ha := hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hn := ((ha.const_mul α).sin).const_mul α
  have hs := sqrt_pos_of_mem hx
  have h := hn.div (hasDerivAt_sqrt_one_sub hx) hs.ne'
  unfold ψ
  convert h using 1
  unfold G
  rw [Real.sin_arccos, Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])]
  field_simp
  ring

lemma deriv2_φ (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv^[2] (φ α) x = -α * G α (Real.arccos x) / √(1 - x ^ 2) ^ 3 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  have heq : deriv (φ α) =ᶠ[nhds x] ψ α := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_φ α hy).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_ψ α hx).deriv

lemma continuous_φ (α : ℝ) : Continuous (φ α) :=
  Real.continuous_cos.comp (continuous_const.mul Real.continuous_arccos)

theorem strictConcaveOn_φ {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) (φ α) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (continuous_φ α).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv2_φ α hx]
  have hs := sqrt_pos_of_mem hx
  have hθ0 : 0 < Real.arccos x := Real.arccos_pos.2 hx.2
  have hθπ : Real.arccos x < π := Real.arccos_lt_pi.2 hx.1
  have hG := G_pos hα0 hα1 hθ0 hθπ
  have : 0 < α * G α (Real.arccos x) / √(1 - x ^ 2) ^ 3 := by positivity
  rw [neg_mul, neg_div]; linarith

/-! ### `f = r_E ∘ arccos` and its integral representation, Eq. (62) -/

def f (x : ℝ) : ℝ := EulerianCert.FourierModes.rE (Real.arccos x)

lemma integral_cos_scaled (θ : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.cos (t / 2 * θ)) = EulerianCert.FourierModes.rE θ := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp
  have hc : θ / 2 ≠ 0 := div_ne_zero hθ two_ne_zero
  have e : (fun t : ℝ => Real.cos (t / 2 * θ)) = fun t => Real.cos (θ / 2 * t) := by
    ext t; ring_nf
  rw [e, intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc, integral_cos,
    mul_zero, Real.sin_zero, sub_zero, mul_one, smul_eq_mul, EulerianCert.FourierModes.rE,
    sinc_of_ne_zero hc]
  field_simp

/-- **Eq. (62)**: `f(x) = ∫₀¹ cos((t/2) arccos x) dt`. -/
theorem f_integral (x : ℝ) : f x = ∫ t in (0 : ℝ)..1, φ (t / 2) x := by
  unfold f φ
  rw [integral_cos_scaled]

lemma continuous_f : Continuous f :=
  EulerianCert.FourierModes.continuous_rE.comp Real.continuous_arccos

/-- **Strict concavity of `f` on `[-1, 1]`** (proof of Theorem 3.12). -/
theorem strictConcaveOn_f : StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) f := by
  refine ⟨convex_Icc _ _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hz : a * x + b * y ∈ Icc (-1 : ℝ) 1 := by
    have := (convex_Icc (-1 : ℝ) 1) hx hy ha.le hb.le hab
    simpa [smul_eq_mul] using this
  rw [f_integral, f_integral, f_integral]
  have hcont : ∀ z : ℝ, Continuous (fun t : ℝ => φ (t / 2) z) := fun z => by
    unfold φ; fun_prop
  have hi1 : IntervalIntegrable (fun t : ℝ => a * φ (t / 2) x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hcont x)).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun t : ℝ => b * φ (t / 2) y) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hcont y)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hi1 hi2]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
    ((continuous_const.mul (hcont x)).add (continuous_const.mul (hcont y))).continuousOn
    (hcont _).continuousOn
  · intro t ht
    have h := (strictConcaveOn_φ (α := t / 2) (by linarith [ht.1]) (by linarith [ht.2])).2 hx hy
      hxy ha hb hab
    simp only [smul_eq_mul] at h
    exact h.le
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have h := (strictConcaveOn_φ (α := 1 / 2) (by norm_num) (by norm_num)).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h
    exact h

/-! ### The minimax line -/

lemma f_neg_one : f (-1) = q := by
  simp [f, Real.arccos_neg_one, EulerianCert.FourierModes.rE_pi, q]

lemma f_one : f 1 = 1 := by simp [f, Real.arccos_one]

def ℓ (x : ℝ) : ℝ := c + m * x

def h (x : ℝ) : ℝ := f x - ℓ x

lemma h_neg_one : h (-1) = 0 := by
  simp only [h, ℓ, f_neg_one, c, m]; ring

lemma h_one : h 1 = 0 := by
  simp only [h, ℓ, f_one, c, m]; ring

lemma continuous_h : Continuous h := by
  unfold h ℓ; exact continuous_f.sub (continuous_const.add (continuous_const.mul continuous_id))

lemma strictConcaveOn_h : StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) h := by
  have hl : ConvexOn ℝ (Icc (-1 : ℝ) 1) ℓ := by
    refine ⟨convex_Icc _ _, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [ℓ, smul_eq_mul]
    have : a * (c + m * x) + b * (c + m * y) = (a + b) * c + m * (a * x + b * y) := by ring
    rw [this, hab]; linarith
  exact strictConcaveOn_f.sub_convexOn hl

lemma h_nonneg {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ h x := by
  have := strictConcaveOn_h.concaveOn.min_le_of_mem_Icc
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) hx
  rw [h_neg_one, h_one, min_self] at this
  exact this

lemma h_zero_pos : 0 < h 0 := by
  have := strictConcaveOn_h.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) (by norm_num : (-1 : ℝ) ≠ 1)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, h_neg_one, h_one] at this
  norm_num at this
  exact this

/-- Existence of the maximiser `x*` of `f − ℓ` on `[-1, 1]`. -/
theorem exists_max : ∃ xs ∈ Icc (-1 : ℝ) 1, IsMaxOn h (Icc (-1 : ℝ) 1) xs :=
  isCompact_Icc.exists_isMaxOn ⟨0, by norm_num, by norm_num⟩ continuous_h.continuousOn

/-- The maximiser, the gap `Δ` and `ε_rad = Δ/2` (Eq. (60)). -/
def xs : ℝ := exists_max.choose
lemma xs_mem : xs ∈ Icc (-1 : ℝ) 1 := exists_max.choose_spec.1
lemma xs_max : IsMaxOn h (Icc (-1 : ℝ) 1) xs := exists_max.choose_spec.2
def Δ : ℝ := h xs
def εrad : ℝ := Δ / 2

lemma Δ_pos : 0 < Δ := lt_of_lt_of_le h_zero_pos (xs_max ⟨by norm_num, by norm_num⟩)

lemma xs_interior : xs ∈ Ioo (-1 : ℝ) 1 := by
  refine ⟨lt_of_le_of_ne xs_mem.1 ?_, lt_of_le_of_ne xs_mem.2 ?_⟩
  · intro e; have := Δ_pos; rw [Δ, ← e, h_neg_one] at this; exact lt_irrefl _ this
  · intro e; have := Δ_pos; rw [Δ, e, h_one] at this; exact lt_irrefl _ this

lemma h_le_Δ {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : h x ≤ Δ := xs_max hx

/-- The maximiser is unique. -/
theorem xs_unique {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (hmax : IsMaxOn h (Icc (-1 : ℝ) 1) y) :
    y = xs :=
  strictConcaveOn_h.eq_of_isMaxOn hmax xs_max hy xs_mem

/-- **Eqs. (60)–(61)**: `ℓ + Δ/2` has uniform error `ε_rad` on `[-1, 1]`, attained at `−1, x*, 1`. -/
theorem minimax_line_error :
    (∀ x ∈ Icc (-1 : ℝ) 1, |f x - (c + εrad + m * x)| ≤ εrad) ∧
    |f (-1) - (c + εrad + m * (-1))| = εrad ∧ |f 1 - (c + εrad + m * 1)| = εrad ∧
    |f xs - (c + εrad + m * xs)| = εrad := by
  have hΔ := Δ_pos
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · have h0 := h_nonneg hx; have h1 := h_le_Δ hx
    simp only [h, ℓ] at h0 h1
    rw [abs_le]; constructor <;> simp only [εrad] <;> linarith
  · have := h_neg_one; simp only [h, ℓ] at this
    rw [show f (-1) - (c + εrad + m * (-1)) = -εrad by linarith, abs_neg,
      abs_of_pos (by simp only [εrad]; linarith)]
  · have := h_one; simp only [h, ℓ] at this
    rw [show f 1 - (c + εrad + m * 1) = -εrad by linarith, abs_neg,
      abs_of_pos (by simp only [εrad]; linarith)]
  · have e : f xs - (c + εrad + m * xs) = εrad := by simp only [εrad, Δ, h, ℓ]; ring
    rw [e, abs_of_pos (by simp only [εrad]; linarith)]

/-- **Theorem 3.12, optimality**: every affine `β + αx` has uniform error at least `ε_rad`. -/
theorem minimax_lower (α β e : ℝ) (he : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - (β + α * x)| ≤ e) :
    εrad ≤ e := by
  have h1 := abs_le.1 (he (-1) ⟨le_rfl, by norm_num⟩)
  have h2 := abs_le.1 (he 1 ⟨by norm_num, le_rfl⟩)
  have h3 := abs_le.1 (he xs xs_mem)
  rw [f_neg_one] at h1; rw [f_one] at h2
  have hx := xs_interior
  have id1 : (1 - xs) / 2 * (q - (β + α * (-1))) + (1 + xs) / 2 * (1 - (β + α * 1)) =
      ℓ xs - (β + α * xs) := by simp only [ℓ, c, m]; ring
  have l1 : 0 < (1 - xs) / 2 := by linarith [hx.2]
  have l2 : 0 < (1 + xs) / 2 := by linarith [hx.1]
  have t1 := mul_le_mul_of_nonneg_left h1.1 l1.le
  have t2 := mul_le_mul_of_nonneg_left h2.1 l2.le
  have hΔ : Δ = f xs - ℓ xs := rfl
  simp only [εrad]
  nlinarith

/-- **Theorem 3.12, uniqueness**: error `ε_rad` forces `α = m`, `β = c + ε_rad`. -/
theorem minimax_unique (α β : ℝ) (he : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - (β + α * x)| ≤ εrad) :
    α = m ∧ β = c + εrad := by
  have hx := xs_interior
  apply EulerianCert.Limacon.affine_unique εrad xs (f xs) α β hx.1 hx.2
  · simp only [εrad, Δ, h, ℓ]; ring
  · have := he (-1) ⟨le_rfl, by norm_num⟩; rwa [f_neg_one] at this
  · have := he 1 ⟨by norm_num, le_rfl⟩; rwa [f_one] at this
  · exact he xs xs_mem

/-- `b_rad > 2 a_rad > 0` (end of Theorem 3.12). -/
theorem rad_convex : 2 * m < c + εrad ∧ 0 < 2 * m := by
  have := EulerianCert.Limacon.c_sub_two_m_pos
  have := EulerianCert.Limacon.m_pos
  have : 0 < εrad := by simp only [εrad]; linarith [Δ_pos]
  constructor <;> linarith

/-! ### Eq. (59): the alternation angle -/

open EulerianCert.Corner (rE')

/-- The derivative of `f` on `(-1, 1)`: `f'(x) = −r_E'(θ)/sin θ`, `θ = arccos x`. -/
lemma hasDerivAt_f {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt f (-rE' (Real.arccos x) / √(1 - x ^ 2)) x := by
  have hθ0 : 0 < Real.arccos x := Real.arccos_pos.2 hx.2
  have ha := hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hr := (EulerianCert.Corner.hasDerivAt_rE hθ0.ne').comp x ha
  have heq : f =ᶠ[nhds x] (EulerianCert.Corner.rE ∘ Real.arccos) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have : Real.arccos y ≠ 0 := (Real.arccos_pos.2 hy.2).ne'
    simp only [f, Function.comp_apply]
    rw [EulerianCert.FourierModes.rE_of_ne_zero this]; rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  convert hr using 1
  ring

lemma hasDerivAt_h {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt h (-rE' (Real.arccos x) / √(1 - x ^ 2) - m) x := by
  have := (hasDerivAt_f hx).sub ((hasDerivAt_id' x).const_mul m |>.const_add c)
  unfold h ℓ
  convert this using 1
  ring

/-- **Eq. (59)**: `θ* = arccos x* ∈ (0, π)` satisfies
`m = (2 sin(θ*/2) − θ* cos(θ*/2))/(θ*² sin θ*)`. -/
theorem alternation_angle :
    0 < Real.arccos xs ∧ Real.arccos xs < π ∧
    m = (2 * Real.sin (Real.arccos xs / 2) - Real.arccos xs * Real.cos (Real.arccos xs / 2)) /
      (Real.arccos xs ^ 2 * Real.sin (Real.arccos xs)) := by
  have hx := xs_interior
  set θ := Real.arccos xs with hθ
  have hθ0 : 0 < θ := Real.arccos_pos.2 hx.2
  have hθπ : θ < π := Real.arccos_lt_pi.2 hx.1
  refine ⟨hθ0, hθπ, ?_⟩
  have hloc : IsLocalMax h xs := xs_max.isLocalMax (Icc_mem_nhds hx.1 hx.2)
  have hd : HasDerivAt h (-rE' θ / √(1 - xs ^ 2) - m) xs := hasDerivAt_h hx
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hs : Real.sin θ = √(1 - xs ^ 2) := Real.sin_arccos xs
  have hsp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  rw [← hs] at h0
  have hm : m = -rE' θ / Real.sin θ := by linarith
  rw [hm]
  unfold EulerianCert.Corner.rE'
  field_simp
  ring

/-- `θ*` is the only solution of Eq. (59) in `(0, π)`. -/
theorem alternation_angle_unique {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π)
    (hm : m = (2 * Real.sin (θ / 2) - θ * Real.cos (θ / 2)) / (θ ^ 2 * Real.sin θ)) :
    θ = Real.arccos xs := by
  -- `x = cos θ` is a critical point of the strictly concave `h` on `(-1, 1)`.
  set x := Real.cos θ with hxdef
  have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
      rwa [Real.cos_pi] at this,
    by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
      rwa [Real.cos_zero] at this⟩
  have harc : Real.arccos x = θ := Real.arccos_cos hθ0.le hθπ.le
  have hsp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hdiff : ∀ y ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ h y := fun y hy =>
    (hasDerivAt_h hy).differentiableAt
  have hderiv : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv h y = -rE' (Real.arccos y) / √(1 - y ^ 2) - m :=
    fun y hy => (hasDerivAt_h hy).deriv
  have hanti := (strictConcaveOn_h.subset Ioo_subset_Icc_self (convex_Ioo _ _)).strictAntiOn_deriv
    hdiff
  have hcrit_x : deriv h x = 0 := by
    rw [hderiv x hx, harc, ← Real.sin_arccos x, harc, hm]
    unfold EulerianCert.Corner.rE'
    field_simp
    ring
  have hcrit_s : deriv h xs = 0 := by
    have hloc : IsLocalMax h xs := xs_max.isLocalMax (Icc_mem_nhds xs_interior.1 xs_interior.2)
    exact hloc.deriv_eq_zero
  have : x = xs := hanti.injOn hx xs_interior (by rw [hcrit_x, hcrit_s])
  rw [← harc, this]

/-! ### Back to the angle variable: `‖r_E − (b + a cos θ)‖_∞` over `[-π, π]` -/

lemma rE_eq_f_cos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : EulerianCert.FourierModes.rE θ = f (Real.cos θ) := by
  unfold f
  rcases le_total 0 θ with h0 | h0
  · rw [Real.arccos_cos h0 hθ.2]
  · rw [← Real.cos_neg, Real.arccos_cos (by linarith) (by linarith [hθ.1]),
      EulerianCert.FourierModes.rE_neg]

lemma f_eq_rE_arccos (x : ℝ) : f x = EulerianCert.FourierModes.rE (Real.arccos x) := rfl

lemma arccos_mem (x : ℝ) : Real.arccos x ∈ Icc (-π) π :=
  ⟨by linarith [Real.arccos_nonneg x, pi_pos], Real.arccos_le_pi x⟩

lemma cos_arccos_of_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : Real.cos (Real.arccos x) = x :=
  Real.cos_arccos hx.1 hx.2

lemma cos_mem (θ : ℝ) : Real.cos θ ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

/-- **Theorem 3.12 in the angle variable**: `b_rad + a_rad cos θ` with `a_rad = m`,
`b_rad = c + ε_rad` has uniform radial error `ε_rad` on `[-π, π]`; every `b + a cos θ` has error
`≥ ε_rad`; equality forces `a = m`, `b = c + ε_rad` (Eq. (61)). -/
theorem radial_minimax :
    (∀ θ ∈ Icc (-π) π,
        |EulerianCert.FourierModes.rE θ - ((c + εrad) + m * Real.cos θ)| ≤ εrad) ∧
    (∀ a b e : ℝ, (∀ θ ∈ Icc (-π) π,
        |EulerianCert.FourierModes.rE θ - (b + a * Real.cos θ)| ≤ e) → εrad ≤ e) ∧
    (∀ a b : ℝ, (∀ θ ∈ Icc (-π) π,
        |EulerianCert.FourierModes.rE θ - (b + a * Real.cos θ)| ≤ εrad) → a = m ∧ b = c + εrad) := by
  have tr : ∀ a b e : ℝ, (∀ θ ∈ Icc (-π) π,
      |EulerianCert.FourierModes.rE θ - (b + a * Real.cos θ)| ≤ e) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |f x - (b + a * x)| ≤ e := by
    intro a b e H x hx
    have := H (Real.arccos x) (arccos_mem x)
    rwa [cos_arccos_of_mem hx, ← f_eq_rE_arccos] at this
  refine ⟨fun θ hθ => ?_, fun a b e H => minimax_lower a b e (tr a b e H),
    fun a b H => minimax_unique a b (tr a b εrad H)⟩
  rw [rE_eq_f_cos hθ]
  have := minimax_line_error.1 (Real.cos θ) (cos_mem θ)
  convert this using 2

end EulerianCert.RadialMinimax
