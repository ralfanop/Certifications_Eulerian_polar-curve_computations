import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Lean certificates of the six displayed decimal values

Manuscript V173: the six decimal occurrences certified by Arb in the 29 October supplement,
now proved in Lean 4.

* (4)  `r_E(π) = 2/π ≈ 0.6366197723675813` (correctly rounded);
* (5)  `p_E = (-2/π, 0)`, `-2/π ≈ -0.6366197723675813`;
* (6)  `ϑ_E = 2 arccot π ≈ 35.3135743028257170°`;
* (12) `d_E = 8/π³ ≈ 0.2580122754655959`;
* (13) `β(3) = π³/32 ≈ 0.9689461462593694`;
* (31) `C_B = (π/e)^{1/4} = 1.0368450238583971902741679669…` (truncated prefix).

"Correctly rounded to the printed digits" is certified as `|value - printed| < ½·10^{-p}`.
`π` is enclosed to `10^{-34}` through Machin's formula `π/4 = 4 arctan(1/5) - arctan(1/239)`
with proved alternating-series bounds for `arctan`; `e` through Taylor's theorem.
-/

open Real Finset intervalIntegral

namespace EulerianBridge.Decimals

/-! ## Alternating partial sums of `arctan` -/

/-- `atS x n = ∑_{k<n} (-1)^k x^{2k+1}/(2k+1)`. -/
noncomputable def atS (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-1:ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

theorem hasDerivAt_atS (x : ℝ) (n : ℕ) :
    HasDerivAt (fun x => atS x n) (∑ k ∈ range n, (-(x ^ 2)) ^ k) x := by
  unfold atS
  have : ∀ k ∈ range n, HasDerivAt (fun x : ℝ => (-1:ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1))
      ((-(x ^ 2)) ^ k) x := by
    intro k _
    have h := ((hasDerivAt_pow (2 * k + 1) x).const_mul ((-1:ℝ) ^ k)).div_const ((2:ℝ) * k + 1)
    convert h using 1
    have hk : (2:ℝ) * k + 1 ≠ 0 := by positivity
    rw [neg_pow, ← pow_mul]
    push_cast
    field_simp
  have hs := HasDerivAt.sum this
  convert hs using 1
  ext y; simp [Finset.sum_apply]

theorem geom_neg_sq (x : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (-(x ^ 2)) ^ k = (1 - (-(x ^ 2)) ^ n) / (1 + x ^ 2) := by
  have h : (-(x ^ 2)) ≠ 1 := by nlinarith [sq_nonneg x]
  rw [geom_sum_eq h]
  have h2 : (1:ℝ) + x ^ 2 ≠ 0 := by positivity
  have h3 : (-(x ^ 2)) - 1 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [div_eq_div_iff h3 h2]
  ring

/-- `arctan x - atS x n = ∫_0^x (-t²)^n/(1+t²) dt`. -/
theorem arctan_sub_atS (x : ℝ) (n : ℕ) :
    arctan x - atS x n = ∫ t in (0:ℝ)..x, (-(t ^ 2)) ^ n / (1 + t ^ 2) := by
  have hd : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun t => arctan t - atS t n)
      ((-(t ^ 2)) ^ n / (1 + t ^ 2)) t := by
    intro t _
    have h := (hasDerivAt_arctan t).sub (hasDerivAt_atS t n)
    convert h using 1
    rw [geom_neg_sq]
    have h2 : (1:ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp [atS]
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t; positivity

theorem arctan_ge_atS_even {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : atS x (2 * n) ≤ arctan x := by
  have := arctan_sub_atS x (2 * n)
  have hnn : 0 ≤ ∫ t in (0:ℝ)..x, (-(t ^ 2)) ^ (2 * n) / (1 + t ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t _
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  linarith

theorem arctan_le_atS_odd {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : arctan x ≤ atS x (2 * n + 1) := by
  have := arctan_sub_atS x (2 * n + 1)
  have hnp : (∫ t in (0:ℝ)..x, (-(t ^ 2)) ^ (2 * n + 1) / (1 + t ^ 2)) ≤ 0 := by
    have h0 : 0 ≤ ∫ t in (0:ℝ)..x, -((-(t ^ 2)) ^ (2 * n + 1) / (1 + t ^ 2)) := by
      apply intervalIntegral.integral_nonneg hx
      intro t _
      rw [neg_nonneg]
      apply div_nonpos_of_nonpos_of_nonneg
      · rw [pow_succ, pow_mul]
        have : 0 ≤ ((-(t ^ 2)) ^ 2) ^ n := by positivity
        nlinarith [sq_nonneg t]
      · positivity
    rw [intervalIntegral.integral_neg] at h0
    linarith
  linarith

/-! ## Machin's formula -/

theorem machin : π / 4 = 4 * arctan (1 / 5) - arctan (1 / 239) := by
  have h2 : 2 * arctan (1 / 5) = arctan (5 / 12) := by
    rw [two_mul, arctan_add (by norm_num)]; norm_num
  have h4 : 4 * arctan (1 / 5) = arctan (120 / 119) := by
    rw [show (4:ℝ) * arctan (1 / 5) = 2 * arctan (1 / 5) + 2 * arctan (1 / 5) by ring, h2,
      arctan_add (by norm_num)]
    norm_num
  rw [h4, sub_eq_add_neg, ← arctan_neg, arctan_add (by norm_num), ← arctan_one]
  norm_num

/-- Rational enclosure of `π` to `10^{-34}`. -/
theorem pi_enclosure :
    (31415926535897932384626433832795028 : ℝ) / 10 ^ 34 < π ∧
      π < (31415926535897932384626433832795029 : ℝ) / 10 ^ 34 := by
  have hm := machin
  have l5 := arctan_ge_atS_even (x := 1 / 5) (by norm_num) 13
  have u5 := arctan_le_atS_odd (x := 1 / 5) (by norm_num) 13
  have l239 := arctan_ge_atS_even (x := 1 / 239) (by norm_num) 4
  have u239 := arctan_le_atS_odd (x := 1 / 239) (by norm_num) 4
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at l5 u5 l239 u239
  norm_num at l5 u5 l239 u239
  constructor <;> linarith

/-! ## Bounds for `e` -/

theorem e_enclosure :
    (27182818284590452353602874713526624 : ℝ) / 10 ^ 34 < exp 1 ∧
      exp 1 < (27182818284590452353602874713526625 : ℝ) / 10 ^ 34 := by
  have h := Real.exp_bound (x := 1) (by norm_num) (n := 34) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

/-! ## The six decimals -/

theorem endpoint_value :
    |2 / π - 0.6366197723675813| < 5 / 10 ^ 17 := by
  obtain ⟨hl, hu⟩ := pi_enclosure
  have hp : 0 < π := pi_pos
  rw [abs_lt]; constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hp]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]; nlinarith

theorem joining_point_value :
    |-(2 / π) - (-0.6366197723675813)| < 5 / 10 ^ 17 := by
  rw [show -(2 / π) - (-0.6366197723675813) = -(2 / π - 0.6366197723675813) by ring, abs_neg]
  exact endpoint_value

theorem determinant_value :
    |8 / π ^ 3 - 0.2580122754655959| < 5 / 10 ^ 17 := by
  obtain ⟨hl, hu⟩ := pi_enclosure
  have hp : 0 < π := pi_pos
  have h3l : ((31415926535897932384626433832795028 : ℝ) / 10 ^ 34) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ hl (by norm_num) (by norm_num)
  have h3u : π ^ 3 < ((31415926535897932384626433832795029 : ℝ) / 10 ^ 34) ^ 3 :=
    pow_lt_pow_left₀ hu hp.le (by norm_num)
  have hp3 : 0 < π ^ 3 := by positivity
  rw [abs_lt]; constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hp3]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hp3]; nlinarith

theorem beta_three_value :
    |π ^ 3 / 32 - 0.9689461462593694| < 5 / 10 ^ 17 := by
  obtain ⟨hl, hu⟩ := pi_enclosure
  have hp : 0 < π := pi_pos
  have h3l : ((31415926535897932384626433832795028 : ℝ) / 10 ^ 34) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ hl (by norm_num) (by norm_num)
  have h3u : π ^ 3 < ((31415926535897932384626433832795029 : ℝ) / 10 ^ 34) ^ 3 :=
    pow_lt_pow_left₀ hu hp.le (by norm_num)
  rw [abs_lt]; constructor <;> norm_num at h3l h3u ⊢ <;> linarith

/-- `arctan(1/π)` enclosed through `1/π` and the alternating series (monotonicity of `arctan`). -/
theorem angle_degrees_value :
    |2 * arctan (1 / π) * 180 / π - 35.3135743028257170| < 5 / 10 ^ 17 := by
  obtain ⟨hl, hu⟩ := pi_enclosure
  have hp : 0 < π := pi_pos
  set pl : ℝ := (31415926535897932384626433832795028 : ℝ) / 10 ^ 34
  set pu : ℝ := (31415926535897932384626433832795029 : ℝ) / 10 ^ 34
  have hpl : 0 < pl := by norm_num [pl]
  -- 1/pu < 1/π < 1/pl
  have i1 : 1 / pu < 1 / π := one_div_lt_one_div_of_lt hp hu
  have i2 : 1 / π < 1 / pl := one_div_lt_one_div_of_lt hpl hl
  have a1 : arctan (1 / pu) < arctan (1 / π) := arctan_strictMono i1
  have a2 : arctan (1 / π) < arctan (1 / pl) := arctan_strictMono i2
  have lA := arctan_ge_atS_even (x := 1 / pu) (by norm_num [pu]) 17
  have uA := arctan_le_atS_odd (x := 1 / pl) (by norm_num [pl]) 17
  simp only [atS, Finset.sum_range_succ, Finset.sum_range_zero] at lA uA
  norm_num [pl, pu] at lA uA hl hu
  have hlo : 2 * arctan (1 / π) * 180 / π > 35.31357430282571695 := by
    rw [gt_iff_lt, lt_div_iff₀ hp]; nlinarith
  have hhi : 2 * arctan (1 / π) * 180 / π < 35.31357430282571705 := by
    rw [div_lt_iff₀ hp]; nlinarith
  rw [abs_lt]; constructor <;> linarith

/-- `C_B = (π/e)^{1/4} ∈ [1.0368450238583971902741679669, 1.0368450238583971902741679670)`. -/
theorem bargmann_constant_value :
    (1.0368450238583971902741679669 : ℝ) ≤ (π / exp 1) ^ ((1:ℝ) / 4) ∧
      (π / exp 1) ^ ((1:ℝ) / 4) < 1.0368450238583971902741679670 := by
  obtain ⟨hl, hu⟩ := pi_enclosure
  obtain ⟨el, eu⟩ := e_enclosure
  have hp : 0 < π := pi_pos
  have he : 0 < exp 1 := exp_pos 1
  have hq : 0 < π / exp 1 := div_pos hp he
  -- the fourth power of the bounds brackets π/e
  have c1 : (1.0368450238583971902741679669 : ℝ) ^ 4 < π / exp 1 := by
    rw [lt_div_iff₀ he]; norm_num at hl eu ⊢; nlinarith
  have c2 : π / exp 1 < (1.0368450238583971902741679670 : ℝ) ^ 4 := by
    rw [div_lt_iff₀ he]; norm_num at hu el ⊢; nlinarith
  have key : ∀ y : ℝ, 0 ≤ y → (y ^ 4) ^ ((1:ℝ) / 4) = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  constructor
  · rw [← key 1.0368450238583971902741679669 (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) c1.le (by norm_num)
  · rw [← key 1.0368450238583971902741679670 (by norm_num)]
    exact Real.rpow_lt_rpow hq.le c2 (by norm_num)

end EulerianBridge.Decimals
