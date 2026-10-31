/-
# The limaçon bodies `Ω_h` are convex; supporting half-planes (used in Theorem 3.13, V001)

For `h ≥ 0` the body `Ω_h` of `HausdorffMinimax` has radius `R_h(t) = c + h + m cos t > 0`, and
`c + h ≥ c > 2m` (the convexity criterion of the manuscript, `b ≥ 2a`).  We prove:
* the trigonometric inequality behind the supporting lines,
  `(B + a cos t)((B + a cos u) cos(t − u) + a sin u sin(t − u)) ≤ (B + a cos u)²` for `B ≥ 2a ≥ 0`,
  via the factorisation `−(1 − cos φ)·K`, `K ≥ 0`;
* for every boundary point `γ_h(t₀)` the outward normal `N(t₀)` gives the supporting half-plane
  `⟨w, N⟩ ≤ R_h(t₀)²` for all `w ∈ Ω_h` (equality at `γ_h(t₀)`);
* `Ω_h` is the intersection of these half-planes, hence convex;
* the polar gauges: a non-zero `z` with `‖z‖ ≤ R_h` (resp. `=`) at its own direction lies in `Ω_h`
  (resp. on `Γ_h`), and with `‖z‖ = r_E` at its direction lies on `Γ_E`;
* the disc of radius `q + h` is contained in `Ω_h`, so `s · γ_h(t)` with `s < 1` is an interior
  point.
-/
import EulerianCert.HausdorffMinimax

open Real Set Metric

noncomputable section

namespace EulerianCert.LimaconConvex

open EulerianCert.Limacon (q c m)
open EulerianCert.HausdorffMinimax

local notation "rE" => EulerianCert.FourierModes.rE

/-! ### Elementary planar facts -/

/-- The Euclidean inner product on `ℂ ≃ ℝ²`. -/
def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

lemma dot_sub_left (z z' w : ℂ) : dot (z - z') w = dot z w - dot z' w := by
  simp only [dot, Complex.sub_re, Complex.sub_im]; ring

lemma dot_add_left (z z' w : ℂ) : dot (z + z') w = dot z w + dot z' w := by
  simp only [dot, Complex.add_re, Complex.add_im]; ring

lemma dot_smul_left (r : ℝ) (z w : ℂ) : dot ((r : ℂ) * z) w = r * dot z w := by
  simp only [dot, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma dot_self (z : ℂ) : dot z z = ‖z‖ ^ 2 := by rw [norm_sq_eq, dot]; ring

lemma abs_dot_le (z w : ℂ) : |dot z w| ≤ ‖z‖ * ‖w‖ := by
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg w),
    ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [sq_abs, norm_sq_eq, norm_sq_eq, dot]
  nlinarith [sq_nonneg (z.re * w.im - z.im * w.re)]

lemma dot_le_norm (z w : ℂ) (hw : ‖w‖ = 1) : dot z w ≤ ‖z‖ := by
  have := le_abs_self (dot z w)
  have := abs_dot_le z w
  rw [hw, mul_one] at this
  linarith

lemma pt_re (r t : ℝ) : (pt r t).re = r * Real.cos t := by
  simp [pt, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma pt_im (r t : ℝ) : (pt r t).im = r * Real.sin t := by
  simp [pt, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma pt_eq_iff (z : ℂ) (r t : ℝ) : pt r t = z ↔ z.re = r * Real.cos t ∧ z.im = r * Real.sin t := by
  constructor
  · rintro rfl; exact ⟨pt_re r t, pt_im r t⟩
  · rintro ⟨h1, h2⟩; apply Complex.ext <;> simp [pt_re, pt_im, h1, h2]

lemma polar_of_ne {z : ℂ} : pt ‖z‖ (Complex.arg z) = z := by
  rw [pt]; exact Complex.norm_mul_exp_arg_mul_I z

lemma arg_mem (z : ℂ) : Complex.arg z ∈ Icc (-π) π :=
  ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩

/-! ### The radius for `h ≥ 0` -/

lemma c_sub_m : c - m = q := by simp only [c, m]; ring

lemma q_pos : 0 < q := by simp only [q]; positivity

lemma R_eq {h : ℝ} (hh : 0 ≤ h) (t : ℝ) : R h t = c + h + m * Real.cos t := by
  unfold R
  apply max_eq_right
  have := EulerianCert.Limacon.m_pos
  nlinarith [Real.neg_one_le_cos t, c_sub_m, q_pos]

lemma R_ge {h : ℝ} (hh : 0 ≤ h) (t : ℝ) : q + h ≤ R h t := by
  rw [R_eq hh]
  have := EulerianCert.Limacon.m_pos
  nlinarith [Real.neg_one_le_cos t, c_sub_m]

lemma R_pos {h : ℝ} (hh : 0 ≤ h) (t : ℝ) : 0 < R h t :=
  lt_of_lt_of_le (by linarith [q_pos]) (R_ge hh t)

/-! ### Polar gauges -/

/-- A non-zero point inside the radius at its own direction belongs to `Ω_h`. -/
lemma mem_Ω_of_gauge {h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ≠ 0)
    (hle : ‖z‖ ≤ c + h + m * (z.re / ‖z‖)) : z ∈ Ω h := by
  rw [← polar_of_ne (z := z)]
  apply mem_Ω_of_le (arg_mem z) (norm_nonneg z)
  rw [R_eq hh, Complex.cos_arg hz]; exact hle

/-- The limaçon `Γ_h = Γ_{m, c+h}`. -/
abbrev Γh (h : ℝ) : Set ℂ := Γ m (c + h)

lemma mem_Γh_of_gauge {h : ℝ} {z : ℂ} (hz : z ≠ 0)
    (heq : ‖z‖ = c + h + m * (z.re / ‖z‖)) : z ∈ Γh h := by
  refine ⟨Complex.arg z, arg_mem z, ?_⟩
  show pt (c + h + m * Real.cos (Complex.arg z)) (Complex.arg z) = z
  rw [Complex.cos_arg hz, ← heq]
  exact polar_of_ne

lemma mem_ΓE_of_gauge {z : ℂ} (hz : z ≠ 0)
    (heq : ‖z‖ = rE (Real.arccos (z.re / ‖z‖))) : z ∈ ΓE := by
  refine ⟨Complex.arg z, arg_mem z, ?_⟩
  show pt (rE (Complex.arg z)) (Complex.arg z) = z
  have h1 := RadialMinimax.rE_eq_f_cos (arg_mem z)
  rw [RadialMinimax.f_eq_rE_arccos, Complex.cos_arg hz, ← heq] at h1
  rw [h1]
  exact polar_of_ne

lemma gauge_pt {r t : ℝ} (hr : 0 < r) : (pt r t).re / ‖pt r t‖ = Real.cos t := by
  rw [pt_re, norm_pt, abs_of_pos hr]; field_simp

/-- Every point `γ_h(τ)`, `τ ∈ ℝ`, lies on `Γ_h` (periodicity). -/
lemma γh_mem {h : ℝ} (hh : 0 ≤ h) (τ : ℝ) : pt (R h τ) τ ∈ Γh h := by
  have hR := R_pos hh τ
  apply mem_Γh_of_gauge (z := pt (R h τ) τ)
  · intro h0; have := congrArg norm h0; rw [norm_pt, norm_zero, abs_of_pos hR] at this
    linarith
  · rw [gauge_pt hR, norm_pt, abs_of_pos hR, R_eq hh]

lemma Γh_subset_Ω {h : ℝ} (hh : 0 ≤ h) : Γh h ⊆ Ω h := by
  rintro _ ⟨t, ht, rfl⟩
  show pt (c + h + m * Real.cos t) t ∈ Ω h
  rw [← R_eq hh]
  apply mem_Ω_of_le ht (R_pos hh t).le le_rfl

/-! ### The supporting-line inequality -/

/-- **Trigonometric core**: for `B ≥ 2a ≥ 0`,
`(B + a cos t)((B + a cos u) cos(t − u) + a sin u sin(t − u)) ≤ (B + a cos u)²`. -/
theorem key_ineq (B a t u : ℝ) (ha : 0 ≤ a) (hB : 2 * a ≤ B) :
    (B + a * Real.cos t) * ((B + a * Real.cos u) * Real.cos (t - u) +
      a * Real.sin u * Real.sin (t - u)) ≤ (B + a * Real.cos u) ^ 2 := by
  set φ := t - u with hφ
  have ht : t = u + φ := by rw [hφ]; ring
  have hcost : Real.cos t = Real.cos u * Real.cos φ - Real.sin u * Real.sin φ := by
    rw [ht, Real.cos_add]
  set C := Real.cos u
  set S := Real.sin u
  set cc := Real.cos φ
  set s := Real.sin φ
  have hCS : C ^ 2 + S ^ 2 = 1 := Real.cos_sq_add_sin_sq u
  have hcs : cc ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  rw [hcost]
  set v := C * (cc + 2) - S * s with hv
  set K := B ^ 2 + a ^ 2 * (1 + cc) + a * B * v with hK
  have hid : (B + a * (C * cc - S * s)) * ((B + a * C) * cc + a * S * s) - (B + a * C) ^ 2 =
      -(1 - cc) * K := by
    rw [hK, hv]
    linear_combination (-(a ^ 2) * s ^ 2) * hCS + (-(a ^ 2) * (1 - C ^ 2)) * hcs
  have hv2 : v ^ 2 ≤ 4 * cc + 5 := by
    have e : v ^ 2 + (C * s + S * (cc + 2)) ^ 2 = 4 * cc + 5 := by
      rw [hv]; linear_combination ((cc + 2) ^ 2 + s ^ 2) * hCS + hcs
    nlinarith [sq_nonneg (C * s + S * (cc + 2))]
  have hc1 : cc ≤ 1 := Real.cos_le_one φ
  have hc2 : -1 ≤ cc := Real.neg_one_le_cos φ
  have h5 : 0 ≤ 5 + cc + 2 * v := by
    by_contra hneg
    push Not at hneg
    have : (5 + cc) ^ 2 < 4 * v ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (by linarith : (0 : ℝ) ≤ 5 - cc)]
  have h4 : 0 ≤ 4 + v := by nlinarith
  have hKnn : 0 ≤ K := by
    set d := B - 2 * a with hd
    have hd0 : 0 ≤ d := by linarith
    have : K = a ^ 2 * (5 + cc + 2 * v) + d * (a * (4 + v) + d) := by
      rw [hK, hd]; ring
    rw [this]
    have : 0 ≤ a * (4 + v) + d := by positivity
    positivity
  have : 0 ≤ (1 - cc) * K := mul_nonneg (by linarith) hKnn
  nlinarith

/-- The outward normal of `Γ_h` at the parameter `t₀`. -/
def N (h t₀ : ℝ) : ℂ :=
  ⟨R h t₀ * Real.cos t₀ - m * Real.sin t₀ * Real.sin t₀,
    R h t₀ * Real.sin t₀ + m * Real.sin t₀ * Real.cos t₀⟩

lemma dot_pt_N (h ρ t t₀ : ℝ) :
    dot (pt ρ t) (N h t₀) =
      ρ * (R h t₀ * Real.cos (t - t₀) + m * Real.sin t₀ * Real.sin (t - t₀)) := by
  simp only [dot, pt_re, pt_im, N, Real.cos_sub, Real.sin_sub]
  ring

lemma dot_γ_N {h : ℝ} (t₀ : ℝ) : dot (pt (R h t₀) t₀) (N h t₀) = R h t₀ ^ 2 := by
  rw [dot_pt_N, sub_self, Real.cos_zero, Real.sin_zero]; ring

/-- **Supporting half-plane**: for `h ≥ 0`, every `w ∈ Ω_h` satisfies `⟨w, N(t₀)⟩ ≤ R_h(t₀)²`. -/
theorem supporting {h : ℝ} (hh : 0 ≤ h) (t₀ : ℝ) {w : ℂ} (hw : w ∈ Ω h) :
    dot w (N h t₀) ≤ R h t₀ ^ 2 := by
  obtain ⟨⟨t, s⟩, ⟨-, hs⟩, rfl⟩ := hw
  simp only at hs ⊢
  rw [dot_pt_N]
  set g := R h t₀ * Real.cos (t - t₀) + m * Real.sin t₀ * Real.sin (t - t₀)
  have hR := R_pos hh t
  rcases le_or_gt g 0 with hg | hg
  · have : s * R h t * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs.1 hR.le) hg
    nlinarith [sq_nonneg (R h t₀)]
  · have key := key_ineq (c + h) m t t₀ EulerianCert.Limacon.m_pos.le
      (by linarith [EulerianCert.Limacon.c_sub_two_m_pos])
    rw [← R_eq hh, ← R_eq hh] at key
    calc s * R h t * g ≤ 1 * R h t * g := by gcongr; exact hs.2
      _ = R h t * g := by ring
      _ ≤ R h t₀ ^ 2 := key

/-- `Ω_h` is the intersection of its supporting half-planes. -/
theorem Ω_eq_iInter {h : ℝ} (hh : 0 ≤ h) :
    Ω h = {z | ∀ t₀ : ℝ, dot z (N h t₀) ≤ R h t₀ ^ 2} := by
  ext z
  constructor
  · intro hz t₀; exact supporting hh t₀ hz
  · intro H
    by_contra hz
    have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ zero_mem_Ω h)
    have hlt : R h (Complex.arg z) < ‖z‖ := by
      by_contra hle; push Not at hle
      exact hz (by rw [← polar_of_ne (z := z)]; exact mem_Ω_of_le (arg_mem z) (norm_nonneg z) hle)
    have := H (Complex.arg z)
    have e : dot z (N h (Complex.arg z)) = ‖z‖ * R h (Complex.arg z) := by
      nth_rewrite 1 [← polar_of_ne (z := z)]
      rw [dot_pt_N, sub_self, Real.cos_zero, Real.sin_zero]; ring
    rw [e] at this
    have hR := R_pos hh (Complex.arg z)
    nlinarith

/-- **`Ω_h` is convex** for `h ≥ 0`. -/
theorem convex_Ω {h : ℝ} (hh : 0 ≤ h) : Convex ℝ (Ω h) := by
  rw [Ω_eq_iInter hh]
  intro x hx y hy a b ha hb hab t₀
  have e : dot (a • x + b • y) (N h t₀) = a * dot x (N h t₀) + b * dot y (N h t₀) := by
    simp only [dot, Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e]
  have := hx t₀; have := hy t₀
  nlinarith

/-! ### Interior points -/

lemma ball_subset_Ω {h : ℝ} (hh : 0 ≤ h) {w : ℂ} (hw : ‖w‖ ≤ q + h) : w ∈ Ω h := by
  rcases eq_or_ne w 0 with rfl | hw0
  · exact zero_mem_Ω h
  rw [← polar_of_ne (z := w)]
  exact mem_Ω_of_le (arg_mem w) (norm_nonneg w) (hw.trans (R_ge hh _))

/-- A point `s · γ_h(t)` with `0 ≤ s < 1` has a neighbourhood inside `Ω_h`. -/
theorem interior_of_lt_one {h : ℝ} (hh : 0 ≤ h) {t s : ℝ} (ht : t ∈ Icc (-π) π)
    (hs0 : 0 ≤ s) (hs1 : s < 1) {v : ℂ} (hv : ‖v‖ ≤ (1 - s) * (q + h)) :
    pt (s * R h t) t + v ∈ Ω h := by
  have hW : pt (R h t) t ∈ Ω h := mem_Ω_of_le ht (R_pos hh t).le le_rfl
  have h1s : 0 < 1 - s := by linarith
  have hv' : (((1 - s)⁻¹ : ℝ) : ℂ) * v ∈ Ω h := by
    apply ball_subset_Ω hh
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h1s)]
    rw [inv_mul_le_iff₀ h1s]; exact hv
  have hconv := convex_Ω hh hW hv' hs0 h1s.le (by ring)
  convert hconv using 1
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this; linarith
  simp only [Complex.real_smul, pt]
  push_cast
  field_simp

end EulerianCert.LimaconConvex
