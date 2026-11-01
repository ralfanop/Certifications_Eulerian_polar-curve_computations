import Bridge.AppendixAGd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Section 10: the sharp Lipschitz constant of `arcsin` on the disks `|z - i| ≤ r`

Manuscript 12, Lemma 10.2, eqs. (287)–(290) (source labels `eg:lem:disk-family`,
`eg:eq:disk-lipschitz`, `eg:eq:disk-metallic`, `eg:eq:disk-boundary`,
`eg:eq:cassini-curvature`).

Certified here (real and complex algebra, no `sorry`):

* (289) the boundary identity: for `z = i + r e^{iθ}` and `s = sin θ`,
  `|1 - z²|² = ((r² + 2 + 4 r s)² + (2 - r²)²) / 2`;
* the two minimum statements behind (287): for `r² - 4r + 2 ≥ 0` the minimum over `s ∈ [-1, 1]`
  is `2 [1 + (1 - r)²]²`, attained at `s = -1`; for `r² - 4r + 2 < 0` (and `r > 0`) the point
  `s* = -(r² + 2)/(4r)` lies in `(-1, 0)`, the square vanishes there, and the minimum is `(2 - r²)²`;
  the coordinates of the two extremal points `z±`;
* the threshold: `2 - √2` is a root of `r² - 4r + 2`, and `r² - 4r + 2 ≥ 0` on `(0, 2 - √2]`;
* (288) the metallic identities: with `n = 2(1 - r)` and `μ = (n + √(n² + 4))/2`,
  `sinh (log μ) = 1 - r`, `cosh (log μ) = √(1 + (1 - r)²)`, `gd (log μ) = arctan (1 - r)`, and
  `sech (log μ) = cos (gd (log μ)) = cos (arctan (1 - r)) = 1/√(1 + (1 - r)²)`;
* (290) the identity `|z² - 1|² = (1 + y²)² + 2x²(y² - 1) + x⁴` and the threshold equation:
  for `0 < t < 1`, `(1 - t²)/(t(1 + t²)) = 1/(1 - t)` iff `t² + 2t - 1 = 0`, whose root is `√2 - 1`.

Not formalised: the maximum modulus principle and the holomorphy of the principal branch of
`arcsin` on a neighbourhood of the disk, which the manuscript's proof uses to reduce the supremum
to the boundary circle, and the implicit-function computation of the curvature (290).
-/

open Real

namespace EulerianBridge.DiskFamily

open EulerianBridge.AppendixA

/-- `|1 - z²|²` in real coordinates. -/
theorem normSq_one_sub_sq (z : ℂ) :
    Complex.normSq (1 - z ^ 2) = (1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
  simp only [Complex.normSq_apply, pow_two, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im]
  ring

theorem boundary_re (r θ : ℝ) :
    (Complex.I + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r * Real.cos θ := by
  simp [Complex.exp_ofReal_mul_I_re]

theorem boundary_im (r θ : ℝ) :
    (Complex.I + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = 1 + r * Real.sin θ := by
  simp [Complex.exp_ofReal_mul_I_im]

/-- Eq. (289): on the circle `z = i + r e^{iθ}`,
`|1 - z²|² = ((r² + 2 + 4 r sin θ)² + (2 - r²)²) / 2`. -/
theorem boundary_identity (r θ : ℝ) :
    Complex.normSq (1 - (Complex.I + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2)
      = ((r ^ 2 + 2 + 4 * r * Real.sin θ) ^ 2 + (2 - r ^ 2) ^ 2) / 2 := by
  rw [normSq_one_sub_sq, boundary_re, boundary_im]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination
    (2 * r ^ 2 * ((1 + r * Real.sin θ) ^ 2 - 1)
      + r ^ 4 * (Real.cos θ ^ 2 + 1 - Real.sin θ ^ 2)) * h

/-- Eq. (287), first case: if `r² - 4r + 2 ≥ 0`, then for every `s ∈ [-1, 1]` the right-hand side
of (289), times 2, is at least `2 [1 + (1 - r)²]²`. -/
theorem min_first_case {r s : ℝ} (hr : 0 < r) (hth : 0 ≤ r ^ 2 - 4 * r + 2)
    (hs1 : -1 ≤ s) (_hs2 : s ≤ 1) :
    2 * (1 + (1 - r) ^ 2) ^ 2 ≤ (r ^ 2 + 2 + 4 * r * s) ^ 2 + (2 - r ^ 2) ^ 2 := by
  have h1 : 0 ≤ r ^ 2 + 2 - 4 * r := by linarith
  have h2 : r ^ 2 + 2 - 4 * r ≤ r ^ 2 + 2 + 4 * r * s := by nlinarith
  have h3 : (r ^ 2 + 2 - 4 * r) ^ 2 ≤ (r ^ 2 + 2 + 4 * r * s) ^ 2 :=
    pow_le_pow_left₀ h1 h2 2
  nlinarith [h3]

/-- Eq. (287), first case: equality at `s = -1`, that is at `z = i(1 - r)`. -/
theorem min_first_case_eq (r : ℝ) :
    (r ^ 2 + 2 + 4 * r * (-1)) ^ 2 + (2 - r ^ 2) ^ 2 = 2 * (1 + (1 - r) ^ 2) ^ 2 := by
  ring

/-- Eq. (287), first case: equality only at `s = -1` when `r > 0` and `r² - 4r + 2 ≥ 0`. -/
theorem min_first_case_unique {r s : ℝ} (hr : 0 < r) (hth : 0 ≤ r ^ 2 - 4 * r + 2)
    (hs1 : -1 ≤ s) (_hs2 : s ≤ 1)
    (heq : (r ^ 2 + 2 + 4 * r * s) ^ 2 + (2 - r ^ 2) ^ 2 = 2 * (1 + (1 - r) ^ 2) ^ 2) :
    s = -1 := by
  have h1 : 0 ≤ r ^ 2 + 2 - 4 * r := by linarith
  have h2 : r ^ 2 + 2 - 4 * r ≤ r ^ 2 + 2 + 4 * r * s := by nlinarith
  have hsq : (r ^ 2 + 2 + 4 * r * s) ^ 2 = (r ^ 2 + 2 - 4 * r) ^ 2 := by nlinarith
  have hpos : 0 ≤ r ^ 2 + 2 + 4 * r * s := le_trans h1 h2
  have habs : r ^ 2 + 2 + 4 * r * s = r ^ 2 + 2 - 4 * r := by
    have := (sq_eq_sq₀ hpos h1).mp hsq
    exact this
  have : 4 * r * (s + 1) = 0 := by linarith
  have hr4 : (4 * r) ≠ 0 := by positivity
  have := (mul_eq_zero.mp this).resolve_left hr4
  linarith

/-- Eq. (287), second case: the critical value `s* = -(r² + 2)/(4r)` lies in `(-1, 0)`. -/
theorem second_case_sstar {r : ℝ} (hr : 0 < r) (hth : r ^ 2 - 4 * r + 2 < 0) :
    -1 < -(r ^ 2 + 2) / (4 * r) ∧ -(r ^ 2 + 2) / (4 * r) < 0 := by
  have h4r : 0 < 4 * r := by positivity
  constructor
  · rw [lt_div_iff₀ h4r]; linarith
  · apply div_neg_of_neg_of_pos _ h4r; nlinarith

/-- Eq. (287), second case: the square vanishes at `s*`, so the minimum of (289) is
`(2 - r²)² / 2`. -/
theorem second_case_value {r : ℝ} (hr : 0 < r) :
    (r ^ 2 + 2 + 4 * r * (-(r ^ 2 + 2) / (4 * r))) ^ 2 + (2 - r ^ 2) ^ 2 = (2 - r ^ 2) ^ 2 := by
  have : r ^ 2 + 2 + 4 * r * (-(r ^ 2 + 2) / (4 * r)) = 0 := by
    field_simp
    ring
  rw [this]; ring

/-- Eq. (287), second case: the lower bound `(2 - r²)²` holds for every `s`. -/
theorem second_case_lower (r s : ℝ) :
    (2 - r ^ 2) ^ 2 ≤ (r ^ 2 + 2 + 4 * r * s) ^ 2 + (2 - r ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (r ^ 2 + 2 + 4 * r * s)]

/-- The extremal points `z± = ±√(16r² - (r² + 2)²)/4 + i(2 - r²)/4`: with `sin θ = s*`,
`Im z = 1 + r s* = (2 - r²)/4` and `(Re z)² = r²(1 - s*²) = (16r² - (r² + 2)²)/16`. -/
theorem extremal_points {r : ℝ} (hr : 0 < r) :
    1 + r * (-(r ^ 2 + 2) / (4 * r)) = (2 - r ^ 2) / 4 ∧
      r ^ 2 * (1 - (-(r ^ 2 + 2) / (4 * r)) ^ 2) = (16 * r ^ 2 - (r ^ 2 + 2) ^ 2) / 16 := by
  constructor
  · field_simp; ring
  · field_simp; ring

/-- The threshold `2 - √2` is a root of `r² - 4r + 2`. -/
theorem threshold_root : (2 - √2) ^ 2 - 4 * (2 - √2) + 2 = 0 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination h

/-- Below the threshold, `r² - 4r + 2 ≥ 0`. -/
theorem below_threshold {r : ℝ} (hr : r ≤ 2 - √2) : 0 ≤ r ^ 2 - 4 * r + 2 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hfac : r ^ 2 - 4 * r + 2 = (r - (2 - √2)) * (r - (2 + √2)) := by
    linear_combination h
  rw [hfac]
  apply mul_nonneg_of_nonpos_of_nonpos <;> linarith

/-- Above the threshold and below `√2`, `r² - 4r + 2 < 0`. -/
theorem above_threshold {r : ℝ} (hr1 : 2 - √2 < r) (hr2 : r < √2) : r ^ 2 - 4 * r + 2 < 0 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hfac : r ^ 2 - 4 * r + 2 = (r - (2 - √2)) * (r - (2 + √2)) := by
    linear_combination h
  rw [hfac]
  apply mul_neg_of_pos_of_neg <;> linarith

/-! ### Eq. (288): the metallic form -/

/-- The metallic root `μ = (n + √(n² + 4))/2` with `n = 2(1 - r)`. -/
noncomputable def mu (r : ℝ) : ℝ := (2 * (1 - r) + √((2 * (1 - r)) ^ 2 + 4)) / 2

theorem sqrt_metallic (r : ℝ) : √((2 * (1 - r)) ^ 2 + 4) = 2 * √(1 + (1 - r) ^ 2) := by
  rw [show (2 * (1 - r)) ^ 2 + 4 = 2 ^ 2 * (1 + (1 - r) ^ 2) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem mu_eq (r : ℝ) : mu r = (1 - r) + √(1 + (1 - r) ^ 2) := by
  unfold mu; rw [sqrt_metallic]; ring

theorem mu_pos (r : ℝ) : 0 < mu r := by
  rw [mu_eq]
  have h : |1 - r| < √(1 + (1 - r) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := neg_abs_le (1 - r)
  linarith

/-- `μ` is the positive root of `μ² - nμ - 1 = 0`, `n = 2(1 - r)`. -/
theorem mu_root (r : ℝ) : mu r ^ 2 - 2 * (1 - r) * mu r - 1 = 0 := by
  rw [mu_eq]
  have h : √(1 + (1 - r) ^ 2) ^ 2 = 1 + (1 - r) ^ 2 := Real.sq_sqrt (by positivity)
  linear_combination h

theorem mu_inv (r : ℝ) : (mu r)⁻¹ = √(1 + (1 - r) ^ 2) - (1 - r) := by
  have h : √(1 + (1 - r) ^ 2) ^ 2 = 1 + (1 - r) ^ 2 := Real.sq_sqrt (by positivity)
  have hprod : mu r * (√(1 + (1 - r) ^ 2) - (1 - r)) = 1 := by
    rw [mu_eq]; linear_combination h
  exact inv_eq_of_mul_eq_one_right hprod

theorem sinh_log_mu (r : ℝ) : Real.sinh (Real.log (mu r)) = 1 - r := by
  rw [Real.sinh_eq, Real.exp_log (mu_pos r), Real.exp_neg, Real.exp_log (mu_pos r), mu_inv, mu_eq]
  ring

theorem cosh_log_mu (r : ℝ) : Real.cosh (Real.log (mu r)) = √(1 + (1 - r) ^ 2) := by
  rw [Real.cosh_eq, Real.exp_log (mu_pos r), Real.exp_neg, Real.exp_log (mu_pos r), mu_inv, mu_eq]
  ring

/-- Eq. (288): `sech (log μ) = cos (gd (log μ)) = cos (arctan (1 - r)) = [1 + (1 - r)²]^{-1/2}`. -/
theorem metallic_form (r : ℝ) :
    (Real.cosh (Real.log (mu r)))⁻¹ = Real.cos (gd (Real.log (mu r))) ∧
      Real.cos (gd (Real.log (mu r))) = Real.cos (Real.arctan (1 - r)) ∧
      Real.cos (Real.arctan (1 - r)) = 1 / √(1 + (1 - r) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gd_eq, sinh_log_mu, cosh_log_mu, Real.cos_arctan, one_div]
  · rw [gd_eq, sinh_log_mu]
  · rw [Real.cos_arctan]

/-- The golden case `r = 1/2`: `μ = (1 + √5)/2` and `L = 2/√5`. -/
theorem golden_case : mu (1 / 2) = (1 + √5) / 2 ∧ 1 / √(1 + (1 - 1 / 2 : ℝ) ^ 2) = 2 / √5 := by
  have h5 : √(5 / 4 : ℝ) = √5 / 2 := by
    rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · rw [mu_eq, show (1 + (1 - 1 / 2 : ℝ) ^ 2) = 5 / 4 by norm_num, h5]; ring
  · rw [show (1 + (1 - 1 / 2 : ℝ) ^ 2) = 5 / 4 by norm_num, h5]
    field_simp

/-- The case `r = 1/4`: `μ = 2` and `L = 4/5`. -/
theorem quarter_case : mu (1 / 4) = 2 ∧ 1 / √(1 + (1 - 1 / 4 : ℝ) ^ 2) = 4 / 5 := by
  have h : √(1 + (1 - 1 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show (1 + (1 - 1 / 4 : ℝ) ^ 2) = (5 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · rw [mu_eq, h]; norm_num
  · rw [h]; norm_num

/-! ### Eq. (290): the contact of curvatures -/

/-- `|z² - 1|² = (1 + y²)² + 2x²(y² - 1) + x⁴` for `z = x + iy`. -/
theorem normSq_sq_sub_one (x y : ℝ) :
    (x ^ 2 - y ^ 2 - 1) ^ 2 + (2 * x * y) ^ 2 = (1 + y ^ 2) ^ 2 + 2 * x ^ 2 * (y ^ 2 - 1) + x ^ 4 := by
  ring

/-- Eq. (290) and the threshold: for `0 < t < 1` and `r = 1 - t`, the curvature
`κ = (1 - t²)/(t(1 + t²))` equals `1/r` iff `t² + 2t - 1 = 0`. -/
theorem curvature_threshold {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t ^ 2) / (t * (1 + t ^ 2)) = 1 / (1 - t) ↔ t ^ 2 + 2 * t - 1 = 0 := by
  have h1 : t * (1 + t ^ 2) ≠ 0 := by positivity
  have h2 : (1 - t) ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- The root of `t² + 2t - 1` in `(0, 1)` is `√2 - 1`, i.e. `r = 2 - √2`. -/
theorem curvature_root : (√2 - 1) ^ 2 + 2 * (√2 - 1) - 1 = 0 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination h

/-- At the threshold, `κ = 1/r = 1 + 1/√2`. -/
theorem curvature_at_threshold : 1 / (2 - √2) = 1 + 1 / √2 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : √2 < 2 := by nlinarith
  have h2 : 2 - √2 ≠ 0 := by linarith
  field_simp
  linear_combination h

end EulerianBridge.DiskFamily
