/-
# V001 Lemma 3.15, Eqs. (85)–(92): asymptotics of the central slopes

`D = n + 1`, `I_D = ∫_ℝ r_E(t)^D (1 − cos t) dt` (Eq. (86)), `s_n = D I_D/(2π)` (Eq. (87),
module `EulerianFourier`).  Using `1 − cos t = (t²/2) r_E(t)²`, `I_D = ½ ∫ t² r_E^{D+2}`, and the
second-order Laplace method gives
* **Eq. (91)**: `I_D = (√π/4)(24/D)^{3/2}(1 − 15/(4D) + O(D^{−2}))`;
* **Eq. (92)**: `s_n = √(216/(πD)) (1 − 15/(4D) + O(D^{−2}))`;
* **Eq. (85)**: `c_n = 1/s_n = √(π(n+1)/216) (1 + 15/(4(n+1)) + O(n^{−2}))`.
Ingredients: Taylor bounds for `sin`, `cos` to order 7, `r_E(t) = exp(−t²/24 − t⁴/2880 + ε)`
with `|ε| ≤ t⁶/10⁴` on `|t| ≤ 1` (Eq. (89)–(90)), the exact Gaussian moments
`∫ t² e^{−bt²} = √π/(2 b^{3/2})`, `∫ t⁶ e^{−bt²} = 15√π/(8 b^{7/2})` (Mathlib's Gamma integrals),
and exponentially small tails (Eq. (88)).
-/
import EulerianCert.LocalLimit
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace EulerianCert.CentralSlope

open EulerianCert.LocalLimit

local notation "rE" => EulerianCert.FourierModes.rE

/-! ### Higher-order Taylor bounds -/

lemma cos_ge {y : ℝ} (hy : 0 ≤ y) : 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 ≤ Real.cos y := by
  have := nonneg_of_deriv_nonneg (f := fun y => Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720)
    (f' := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y)
    (fun x => by
      have := (((((hasDerivAt_cos x).sub (hasDerivAt_const x (1 : ℝ))).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 4 x).div_const 24)).add
        ((hasDerivAt_pow 6 x).div_const 720))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := LocalLimit.sin_le hx; linarith) hy
  linarith

lemma sin_ge7 {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 ≤ Real.sin y := by
  have := nonneg_of_deriv_nonneg
    (f := fun y => Real.sin y - y + y ^ 3 / 6 - y ^ 5 / 120 + y ^ 7 / 5040)
    (f' := fun y => Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720)
    (fun x => by
      have := (((((hasDerivAt_sin x).sub (hasDerivAt_id' x)).add
        ((hasDerivAt_pow 3 x).div_const 6)).sub ((hasDerivAt_pow 5 x).div_const 120)).add
        ((hasDerivAt_pow 7 x).div_const 5040))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := cos_ge hx; linarith) hy
  linarith

lemma rE_ge6 (t : ℝ) : 1 - t ^ 2 / 24 + t ^ 4 / 1920 - t ^ 6 / 322560 ≤ rE t := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [EulerianCert.FourierModes.rE]
  · rw [rE_eq_abs t h]
    have hy : 0 < |t| / 2 := by positivity
    rw [le_div_iff₀ hy]
    have := sin_ge7 hy.le
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
    have h6 : |t| ^ 6 = t ^ 6 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2, ← pow_mul]
    nlinarith

/-! ### Exponential bounds -/

/-- `f(0) = 0`, `f' ≤ 0` on `(−∞, 0]` give `f ≥ 0` on `(−∞, 0]`. -/
lemma nonneg_of_deriv_nonpos_left {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, x ≤ 0 → f' x ≤ 0) {x : ℝ} (hx : x ≤ 0) : 0 ≤ f x := by
  have := nonneg_of_deriv_nonneg (f := fun y => f (-y)) (f' := fun y => -f' (-y))
    (fun y => by
      have := (hf (-y)).comp y (hasDerivAt_neg y)
      exact this.congr_deriv (by ring))
    (by simp [h0]) (fun y hy => by have := hd (-y) (by linarith); linarith) (by linarith : 0 ≤ -x)
  simpa using this

lemma exp_le_quad {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  have := nonneg_of_deriv_nonpos_left (f := fun x => 1 + x + x ^ 2 / 2 - Real.exp x)
    (f' := fun x => 1 + x - Real.exp x)
    (fun y => by
      have := (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id' y)).add
        ((hasDerivAt_pow 2 y).div_const 2)).sub (Real.hasDerivAt_exp y)
      convert this using 1; push_cast; ring)
    (by simp) (fun y _ => by linarith [Real.add_one_le_exp y]) hx
  linarith

lemma exp_ge_cubic {x : ℝ} (hx : x ≤ 0) : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have := nonneg_of_deriv_nonpos_left (f := fun x => Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6)
    (f' := fun x => Real.exp x - 1 - x - x ^ 2 / 2)
    (fun y => by
      have := ((((Real.hasDerivAt_exp y).sub (hasDerivAt_const y (1 : ℝ))).sub
        (hasDerivAt_id' y)).sub ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((hasDerivAt_pow 3 y).div_const 6)
      convert this using 1; push_cast; ring)
    (by simp) (fun y hy => by have := exp_le_quad hy; linarith) hx
  linarith

/-- `|e^z − 1 − z| ≤ z² e^{|z|}`. -/
lemma abs_exp_sub_one_sub (z : ℝ) : |Real.exp z - 1 - z| ≤ z ^ 2 * Real.exp |z| := by
  have h1 := Real.add_one_le_exp z
  rcases le_total z 0 with h | h
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos h]
    have := exp_le_quad h
    have : 1 ≤ Real.exp (-z) := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg z]
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg h]
    -- `e^z − 1 − z ≤ (z²/2) e^z` for `z ≥ 0`
    have key := nonneg_of_deriv_nonneg
      (f := fun z => z ^ 2 / 2 * Real.exp z - Real.exp z + 1 + z)
      (f' := fun z => Real.exp z * (z + z ^ 2 / 2 - 1) + 1)
      (fun y => by
        have := (((((hasDerivAt_pow 2 y).div_const 2).mul (Real.hasDerivAt_exp y)).sub
          (Real.hasDerivAt_exp y)).add_const 1).add (hasDerivAt_id' y)
        refine this.congr_deriv ?_
        simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
        ring)
      (by simp)
      (fun y hy => by
        have h2 := Real.add_one_le_exp (-y)
        have h3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
        have h4 := Real.exp_pos y
        nlinarith [sq_nonneg y])
      h
    nlinarith [Real.exp_pos z, sq_nonneg z]

/-! ### `r_E(t) = exp(−t²/24 − t⁴/2880 + ε)`, `|ε| ≤ t⁶/10⁴` on `|t| ≤ 1` (Eqs. (89)–(90)) -/

/-- The constant `K = 10⁻⁴` of the sixth-order error. -/
def Kε : ℝ := 1 / 10000

lemma rE_lower6 {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp (-(t ^ 2 / 24) - t ^ 4 / 2880 - Kε * t ^ 6) ≤ rE t := by
  set s := t ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg t
  have hs1 : s ≤ 1 := by
    have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2; simpa [hs] using this
  have e4 : t ^ 4 = s ^ 2 := by rw [hs]; ring
  have e6 : t ^ 6 = s ^ 3 := by rw [hs]; ring
  rw [e4, e6]
  refine le_trans (exp_le_quad (by unfold Kε; nlinarith [pow_nonneg hs0 3])) ?_
  refine le_trans ?_ (rE_ge6 t)
  rw [← hs, e4, e6]
  have p4 : s ^ 4 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p5 : s ^ 5 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p6 : s ^ 6 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  unfold Kε
  nlinarith [pow_nonneg hs0 4, pow_nonneg hs0 5, pow_nonneg hs0 6]

lemma rE_upper6 {t : ℝ} (ht : |t| ≤ 1) :
    rE t ≤ Real.exp (-(t ^ 2 / 24) - t ^ 4 / 2880 + Kε * t ^ 6) := by
  set s := t ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg t
  have hs1 : s ≤ 1 := by
    have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2; simpa [hs] using this
  have e4 : t ^ 4 = s ^ 2 := by rw [hs]; ring
  have e6 : t ^ 6 = s ^ 3 := by rw [hs]; ring
  have hx : -(s / 24) - s ^ 2 / 2880 + Kε * s ^ 3 ≤ 0 := by
    unfold Kε; nlinarith [pow_le_pow_of_le_one hs0 hs1 (show 1 ≤ 3 by norm_num), pow_nonneg hs0 2]
  rw [e4, e6]
  refine le_trans (rE_le t) (le_trans ?_ (exp_ge_cubic hx))
  rw [← hs, e4]
  have p4 : s ^ 4 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p5 : s ^ 5 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p6 : s ^ 6 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p7 : s ^ 7 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p8 : s ^ 8 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p9 : s ^ 9 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have p3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  unfold Kε
  nlinarith [pow_nonneg hs0 4, pow_nonneg hs0 5, pow_nonneg hs0 6, pow_nonneg hs0 7,
    pow_nonneg hs0 8, pow_nonneg hs0 9]

/-! ### Gaussian moments -/

/-- `M_k = ∫ s^{2k} e^{−s²} ds`. -/
def Mom (k : ℕ) : ℝ := ∫ s : ℝ, s ^ (2 * k) * Real.exp (-1 * s ^ 2)

lemma integrable_mom {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ (2 * k) * Real.exp (-b * t ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 * k : ℕ))
    (by have : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
  refine this.congr (Eventually.of_forall (fun t => ?_))
  beta_reduce
  rw [Real.rpow_natCast]

lemma integral_mom {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ t : ℝ, t ^ (2 * k) * Real.exp (-b * t ^ 2) = Mom k / (b ^ k * √b) := by
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  have h := Measure.integral_comp_mul_left (fun s : ℝ => s ^ (2 * k) * Real.exp (-1 * s ^ 2)) (√b)
  have e : (fun x : ℝ => (√b * x) ^ (2 * k) * Real.exp (-1 * (√b * x) ^ 2)) =
      fun x => b ^ k * (x ^ (2 * k) * Real.exp (-b * x ^ 2)) := by
    funext x
    have : √b ^ 2 = b := Real.sq_sqrt hb.le
    rw [mul_pow, mul_pow, pow_mul, this]; ring_nf
  rw [e, integral_const_mul, abs_of_pos (inv_pos.mpr hsb), smul_eq_mul] at h
  unfold Mom
  rw [eq_div_iff (by positivity)]
  calc (∫ t : ℝ, t ^ (2 * k) * Real.exp (-b * t ^ 2)) * (b ^ k * √b)
      = (b ^ k * ∫ t : ℝ, t ^ (2 * k) * Real.exp (-b * t ^ 2)) * √b := by ring
    _ = ((√b)⁻¹ * ∫ s : ℝ, s ^ (2 * k) * Real.exp (-1 * s ^ 2)) * √b := by rw [h]
    _ = ∫ s : ℝ, s ^ (2 * k) * Real.exp (-1 * s ^ 2) := by field_simp

lemma Mom_eq_Gamma (k : ℕ) : Mom k = Real.Gamma (k + 1 / 2) := by
  unfold Mom
  have h := integral_comp_abs (f := fun s : ℝ => s ^ (2 * k) * Real.exp (-1 * s ^ 2))
  have e1 : (fun x : ℝ => |x| ^ (2 * k) * Real.exp (-1 * |x| ^ 2)) =
      fun x => x ^ (2 * k) * Real.exp (-1 * x ^ 2) := by
    funext x; rw [pow_mul, sq_abs, ← pow_mul]
  rw [e1] at h
  rw [h]
  have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 * k : ℕ)) (b := 1)
    (by norm_num) (by have : (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
                      linarith) (by norm_num)
  have e2 : ∫ x in Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-1 * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    beta_reduce
    rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e2, hg, Real.one_rpow, one_mul]
  push_cast
  rw [show ((2 * (k : ℝ) + 1) / 2) = (k : ℝ) + 1 / 2 by ring]
  ring

lemma Mom_one : Mom 1 = √π / 2 := by
  rw [Mom_eq_Gamma]
  have := Real.Gamma_nat_add_one_add_half 0
  simp only [CharP.cast_eq_zero, zero_add, Nat.doubleFactorial, Nat.cast_one,
    one_mul, pow_one] at this
  push_cast; rw [show (1 : ℝ) + 1 / 2 = 1 + 1 / 2 from rfl]; linarith [this]

lemma Mom_three : Mom 3 = 15 * √π / 8 := by
  rw [Mom_eq_Gamma]
  have := Real.Gamma_nat_add_one_add_half 2
  push_cast at this ⊢
  rw [show (3 : ℝ) + 1 / 2 = 2 + 1 + 1 / 2 by norm_num, this]
  norm_num [Nat.doubleFactorial]

lemma Mom_nonneg (k : ℕ) : 0 ≤ Mom k := by
  unfold Mom
  exact integral_nonneg (fun s => by
    have : 0 ≤ s ^ (2 * k) := by rw [pow_mul]; positivity
    positivity)

/-! ### The second-order pointwise estimate -/

/-- The main term `t² e^{−mt²/24} (1 − m t⁴/2880)`. -/
def Main (m : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * 1) * Real.exp (-((m : ℝ) / 24) * t ^ 2) -
    (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 24) * t ^ 2))

/-- `c₁ = 2 (1/2880² + K²)`. -/
def c1 : ℝ := 2 * (1 / 2880 ^ 2 + Kε ^ 2)

/-- The dominating function of `|t² r_E^m − Main|`. -/
def H2 (m : ℕ) (t : ℝ) : ℝ :=
  c1 * (m : ℝ) ^ 2 * (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
    Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
    (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹) +
    Real.exp (-((m : ℝ) / 48)) * (t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2) +
      (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2)))

lemma Kε_pos : 0 < Kε := by unfold Kε; norm_num

lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma absorb32 {m t : ℝ} (hm0 : 0 ≤ m) (h4 : m * t ^ 4 ≤ m * t ^ 2) (h6 : m * t ^ 6 ≤ m * t ^ 2)
    (hs : 0 ≤ m * t ^ 2) :
    -(m / 24) * t ^ 2 + (m * t ^ 4 / 2880 + m * Kε * t ^ 6) ≤ -(m / 32) * t ^ 2 := by
  unfold Kε
  have e : m * (1 / 10000) * t ^ 6 = (m * t ^ 6) / 10000 := by ring
  rw [e]
  linarith

set_option maxHeartbeats 1000000 in
lemma pointwise2 {m : ℕ} (hm : 4 ≤ m) (t : ℝ) :
    |t ^ 2 * rE t ^ m - Main m t| ≤ H2 m t := by
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hK := Kε_pos
  have hc1 : 0 ≤ c1 := by unfold c1; positivity
  have T1 : 0 ≤ c1 * (m : ℝ) ^ 2 * (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) := by
    have : 0 ≤ t ^ (2 * 5) := by rw [pow_mul]; positivity
    positivity
  have T2 : 0 ≤ Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) := by
    have : 0 ≤ t ^ (2 * 4) := by rw [pow_mul]; positivity
    positivity
  have T3 : 0 ≤ (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹) := by positivity
  have T4 : 0 ≤ Real.exp (-((m : ℝ) / 48)) * (t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2) +
      (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2))) := by
    have : 0 ≤ t ^ (2 * 3) := by rw [pow_mul]; positivity
    have : 0 ≤ t ^ (2 * 1) := by rw [pow_mul]; positivity
    positivity
  set g0 := Real.exp (-((m : ℝ) / 24) * t ^ 2)
  have hg0 : 0 < g0 := Real.exp_pos _
  have hMain : Main m t = t ^ 2 * (g0 * (1 - (m : ℝ) * t ^ 4 / 2880)) := by
    unfold Main; simp only [g0]; ring
  by_cases ht : |t| ≤ 1
  · have ht2 : t ^ 2 ≤ 1 := by
      have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2; simpa using this
    have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
    have ht4 : t ^ 4 ≤ t ^ 2 := by
      rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring]; exact mul_le_of_le_one_right hs0 ht2
    have ht6 : t ^ 6 ≤ t ^ 2 := by
      rw [show t ^ 6 = t ^ 2 * t ^ 4 by ring]
      exact mul_le_of_le_one_right hs0 (ht4.trans ht2)
    have ht12 : t ^ 12 ≤ t ^ 8 := by
      rw [show t ^ 12 = t ^ 8 * t ^ 4 by ring]
      exact mul_le_of_le_one_right (by positivity) (ht4.trans ht2)
    set A := (m : ℝ) * t ^ 4 / 2880
    set B := (m : ℝ) * Kε * t ^ 6
    have hA : 0 ≤ A := by positivity
    have hB : 0 ≤ B := by positivity
    set w := A + B
    -- two-sided exponential bounds for `r_E^m`
    have hlo : g0 * Real.exp (-A - B) ≤ rE t ^ m := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le (rE_lower6 ht) m
      rw [← Real.exp_nat_mul] at this
      refine le_trans (le_of_eq ?_) this
      simp only [g0, A, B]; rw [← Real.exp_add]; congr 1; ring
    have hhi : rE t ^ m ≤ g0 * Real.exp (-A + B) := by
      have := pow_le_pow_left₀ (rE_nonneg (ht.trans (by linarith [pi_gt_three]))) (rE_upper6 ht) m
      rw [← Real.exp_nat_mul] at this
      refine this.trans (le_of_eq ?_)
      simp only [g0, A, B]; rw [← Real.exp_add]; congr 1; ring
    have e1 := abs_exp_sub_one_sub (-A - B)
    have e2 := abs_exp_sub_one_sub (-A + B)
    have hw1 : |-A - B| ≤ w := by rw [abs_le]; constructor <;> linarith
    have hw2 : |-A + B| ≤ w := by rw [abs_le]; constructor <;> linarith
    have hsq1 : (-A - B) ^ 2 ≤ w ^ 2 := by
      have := sq_le_sq' (abs_le.mp hw1).1 (abs_le.mp hw1).2; simpa using this
    have hsq2 : (-A + B) ^ 2 ≤ w ^ 2 := by
      have := sq_le_sq' (abs_le.mp hw2).1 (abs_le.mp hw2).2; simpa using this
    have hexp1 : Real.exp |-A - B| ≤ Real.exp w := Real.exp_le_exp.mpr hw1
    have hexp2 : Real.exp |-A + B| ≤ Real.exp w := Real.exp_le_exp.mpr hw2
    have hb1 : |Real.exp (-A - B) - 1 - (-A - B)| ≤ w ^ 2 * Real.exp w :=
      e1.trans (mul_le_mul hsq1 hexp1 (Real.exp_pos _).le (sq_nonneg _))
    have hb2 : |Real.exp (-A + B) - 1 - (-A + B)| ≤ w ^ 2 * Real.exp w :=
      e2.trans (mul_le_mul hsq2 hexp2 (Real.exp_pos _).le (sq_nonneg _))
    -- `|r^m − g0(1 − A)| ≤ g0 (w² e^w + B)`
    have hcore : |rE t ^ m - g0 * (1 - (m : ℝ) * t ^ 4 / 2880)| ≤
        g0 * (w ^ 2 * Real.exp w + B) := by
      have hA' : (m : ℝ) * t ^ 4 / 2880 = A := rfl
      rw [hA', abs_le]
      have l1 := (abs_le.mp hb1).1
      have u2 := (abs_le.mp hb2).2
      constructor
      · have := mul_le_mul_of_nonneg_left l1 hg0.le
        nlinarith
      · have := mul_le_mul_of_nonneg_left u2 hg0.le
        nlinarith
    -- absorb into the Gaussian `e^{−mt²/32}`
    have hm0 : (0 : ℝ) ≤ m := by linarith
    have hg32 : g0 * Real.exp w ≤ Real.exp (-((m : ℝ) / 32) * t ^ 2) := by
      simp only [g0, w, A, B]; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      exact absorb32 hm0 (mul_le_mul_of_nonneg_left ht4 hm0) (mul_le_mul_of_nonneg_left ht6 hm0)
        (mul_nonneg hm0 hs0)
    have hg32' : g0 ≤ Real.exp (-((m : ℝ) / 32) * t ^ 2) := by
      simp only [g0]; apply Real.exp_le_exp.mpr
      have := mul_nonneg hm0 hs0
      have e1 : -((m : ℝ) / 24) * t ^ 2 = -((m : ℝ) * t ^ 2) / 24 := by ring
      have e2 : -((m : ℝ) / 32) * t ^ 2 = -((m : ℝ) * t ^ 2) / 32 := by ring
      rw [e1, e2]; linarith
    have hw2b : w ^ 2 ≤ c1 * (m : ℝ) ^ 2 * t ^ 8 := by
      have h1 := sq_add_le_two A B
      have h2 : 2 * A ^ 2 = 2 / 2880 ^ 2 * ((m : ℝ) ^ 2 * t ^ 8) := by simp only [A]; ring
      have h3 : 2 * B ^ 2 = 2 * Kε ^ 2 * ((m : ℝ) ^ 2 * t ^ 12) := by simp only [B]; ring
      have h4 : (m : ℝ) ^ 2 * t ^ 12 ≤ (m : ℝ) ^ 2 * t ^ 8 :=
        mul_le_mul_of_nonneg_left ht12 (sq_nonneg _)
      have h5 : c1 * (m : ℝ) ^ 2 * t ^ 8 = 2 / 2880 ^ 2 * ((m : ℝ) ^ 2 * t ^ 8) +
          2 * Kε ^ 2 * ((m : ℝ) ^ 2 * t ^ 8) := by unfold c1; ring
      have hK2 : 0 ≤ 2 * Kε ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h4 hK2
      simp only [w]
      linarith
    have hfinal : t ^ 2 * (g0 * (w ^ 2 * Real.exp w + B)) ≤
        c1 * (m : ℝ) ^ 2 * (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
          Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) := by
      have h1 : t ^ 2 * (g0 * (w ^ 2 * Real.exp w)) ≤
          c1 * (m : ℝ) ^ 2 * (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) := by
        calc t ^ 2 * (g0 * (w ^ 2 * Real.exp w)) = t ^ 2 * w ^ 2 * (g0 * Real.exp w) := by ring
          _ ≤ t ^ 2 * (c1 * (m : ℝ) ^ 2 * t ^ 8) * Real.exp (-((m : ℝ) / 32) * t ^ 2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hw2b hs0) hg32 (by positivity) (by positivity)
          _ = _ := by ring
      have h2 : t ^ 2 * (g0 * B) ≤
          Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) := by
        calc t ^ 2 * (g0 * B) = (Kε * (m : ℝ) * t ^ 8) * g0 := by simp only [B]; ring
          _ ≤ (Kε * (m : ℝ) * t ^ 8) * Real.exp (-((m : ℝ) / 32) * t ^ 2) :=
              mul_le_mul_of_nonneg_left hg32' (by positivity)
          _ = _ := by ring
      nlinarith
    rw [hMain, ← mul_sub, abs_mul, abs_of_nonneg hs0]
    have := mul_le_mul_of_nonneg_left hcore hs0
    unfold H2
    linarith
  · push Not at ht
    have ht2 : 1 ≤ t ^ 2 := by
      have := mul_le_mul ht.le ht.le zero_le_one (abs_nonneg _); rwa [one_mul, ← sq, sq_abs] at this
    have hr := abs_rE_le_far ht.le
    have hr2 : |rE t| ^ (1 + 1) ≤ 8 * (4 + t ^ 2)⁻¹ :=
      EulerianCert.EulerianFourier.pow_rE_le (n := 1) le_rfl t
    have hr4 : |rE t| ^ 4 ≤ 64 * ((4 + t ^ 2)⁻¹) ^ 2 := by
      rw [show (4 : ℕ) = (1 + 1) * 2 from rfl, pow_mul]
      calc (|rE t| ^ (1 + 1)) ^ 2 ≤ (8 * (4 + t ^ 2)⁻¹) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hr2 2
        _ = 64 * ((4 + t ^ 2)⁻¹) ^ 2 := by ring
    have hpart1 : |t ^ 2 * rE t ^ m| ≤ (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t), abs_pow,
        show m = (m - 4) + 4 by omega, pow_add, show m - 4 + 4 - 4 = m - 4 by omega]
      have h4 : 0 < 4 + t ^ 2 := by positivity
      have hq : t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2 ≤ (4 + t ^ 2)⁻¹ := by
        rw [show t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2 = (t ^ 2 / (4 + t ^ 2)) * (4 + t ^ 2)⁻¹ by
          field_simp]
        apply mul_le_of_le_one_left (by positivity)
        rw [div_le_one h4]; linarith
      calc t ^ 2 * (|rE t| ^ (m - 4) * |rE t| ^ 4)
          ≤ t ^ 2 * ((24 / 25 : ℝ) ^ (m - 4) * (64 * ((4 + t ^ 2)⁻¹) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
            exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hr _) hr4 (by positivity)
              (by positivity)
        _ = (24 / 25 : ℝ) ^ (m - 4) * 64 * (t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2) := by ring
        _ ≤ (24 / 25 : ℝ) ^ (m - 4) * 64 * (4 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by ring
    have hpart2 : |Main m t| ≤ Real.exp (-((m : ℝ) / 48)) *
        (t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2) +
          (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2))) := by
      have hg : g0 ≤ Real.exp (-((m : ℝ) / 48)) * Real.exp (-((m : ℝ) / 48) * t ^ 2) := by
        simp only [g0]; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      rw [hMain, abs_mul, abs_of_nonneg (sq_nonneg t), abs_mul, abs_of_pos hg0]
      have h1 : |1 - (m : ℝ) * t ^ 4 / 2880| ≤ 1 + (m : ℝ) * t ^ 4 / 2880 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t ^ 2)]
      calc t ^ 2 * (g0 * |1 - (m : ℝ) * t ^ 4 / 2880|)
          ≤ t ^ 2 * (g0 * (1 + (m : ℝ) * t ^ 4 / 2880)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
            exact mul_le_mul_of_nonneg_left h1 hg0.le
        _ = (t ^ 2 + (m : ℝ) / 2880 * t ^ 6) * g0 := by ring
        _ ≤ (t ^ 2 + (m : ℝ) / 2880 * t ^ 6) *
            (Real.exp (-((m : ℝ) / 48)) * Real.exp (-((m : ℝ) / 48) * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
        _ = _ := by ring
    calc |t ^ 2 * rE t ^ m - Main m t| ≤ |t ^ 2 * rE t ^ m| + |Main m t| := abs_sub _ _
      _ ≤ H2 m t := by unfold H2; linarith

/-! ### Integrals -/

lemma pow_mul_bound_k (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ c, ∀ D : ℕ, (D : ℝ) ^ k * r ^ D ≤ c := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rwa [abs_of_nonneg hr0])
  obtain ⟨c, hc⟩ := h.bddAbove_range
  exact ⟨c, fun D => hc ⟨D, rfl⟩⟩

/-- `∫ 64/(4 + t²) dt`. -/
def J64 : ℝ := ∫ t : ℝ, 64 * (4 + t ^ 2)⁻¹

lemma integrable_J64 : Integrable (fun t : ℝ => 64 * (4 + t ^ 2)⁻¹) := by
  have := integrable_J8.const_mul 8
  refine this.congr (Eventually.of_forall (fun t => ?_))
  beta_reduce; ring

lemma J64_nonneg : 0 ≤ J64 := integral_nonneg (fun t => by positivity)

lemma integral_H2 {m : ℕ} (hm : 1 ≤ m) :
    ∫ t, H2 m t = c1 * (m : ℝ) ^ 2 * (Mom 5 / (((m : ℝ) / 32) ^ 5 * √((m : ℝ) / 32))) +
      Kε * (m : ℝ) * (Mom 4 / (((m : ℝ) / 32) ^ 4 * √((m : ℝ) / 32))) +
      (24 / 25 : ℝ) ^ (m - 4) * J64 +
      Real.exp (-((m : ℝ) / 48)) * (Mom 1 / (((m : ℝ) / 48) ^ 1 * √((m : ℝ) / 48)) +
        (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * √((m : ℝ) / 48)))) := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb1 : (0 : ℝ) < (m : ℝ) / 32 := by positivity
  have hb2 : (0 : ℝ) < (m : ℝ) / 48 := by positivity
  unfold H2
  have i1 : Integrable (fun t : ℝ => c1 * (m : ℝ) ^ 2 *
      (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2))) := (integrable_mom hb1 5).const_mul _
  have i2 : Integrable (fun t : ℝ => Kε * (m : ℝ) *
      (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2))) := (integrable_mom hb1 4).const_mul _
  have i3 : Integrable (fun t : ℝ => (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹)) :=
    integrable_J64.const_mul _
  have i4a : Integrable (fun t : ℝ => t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2)) :=
    integrable_mom hb2 1
  have i4b : Integrable (fun t : ℝ => (m : ℝ) / 2880 *
      (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2))) := (integrable_mom hb2 3).const_mul _
  have i4 : Integrable (fun t : ℝ => Real.exp (-((m : ℝ) / 48)) *
      (t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2) +
        (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2)))) :=
    (i4a.add i4b).const_mul _
  have i12 : Integrable (fun t : ℝ => c1 * (m : ℝ) ^ 2 *
      (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
      Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2))) := i1.add i2
  have i123 : Integrable (fun t : ℝ => c1 * (m : ℝ) ^ 2 *
      (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
      Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) +
      (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹)) := i12.add i3
  have e1 : ∫ t : ℝ, c1 * (m : ℝ) ^ 2 * (t ^ (2 * 5) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) =
      c1 * (m : ℝ) ^ 2 * (Mom 5 / (((m : ℝ) / 32) ^ 5 * √((m : ℝ) / 32))) := by
    rw [integral_const_mul, integral_mom hb1]
  have e2 : ∫ t : ℝ, Kε * (m : ℝ) * (t ^ (2 * 4) * Real.exp (-((m : ℝ) / 32) * t ^ 2)) =
      Kε * (m : ℝ) * (Mom 4 / (((m : ℝ) / 32) ^ 4 * √((m : ℝ) / 32))) := by
    rw [integral_const_mul, integral_mom hb1]
  have e3 : ∫ t : ℝ, (24 / 25 : ℝ) ^ (m - 4) * (64 * (4 + t ^ 2)⁻¹) =
      (24 / 25 : ℝ) ^ (m - 4) * J64 := integral_const_mul _ _
  have e4 : ∫ t : ℝ, Real.exp (-((m : ℝ) / 48)) *
      (t ^ (2 * 1) * Real.exp (-((m : ℝ) / 48) * t ^ 2) +
        (m : ℝ) / 2880 * (t ^ (2 * 3) * Real.exp (-((m : ℝ) / 48) * t ^ 2))) =
      Real.exp (-((m : ℝ) / 48)) * (Mom 1 / (((m : ℝ) / 48) ^ 1 * √((m : ℝ) / 48)) +
        (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * √((m : ℝ) / 48)))) := by
    rw [integral_const_mul, integral_add i4a i4b, integral_const_mul, integral_mom hb2,
      integral_mom hb2]
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, e1, e2, e3, e4]

lemma integrable_H2 {m : ℕ} (hm : 1 ≤ m) : Integrable (H2 m) := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb1 : (0 : ℝ) < (m : ℝ) / 32 := by positivity
  have hb2 : (0 : ℝ) < (m : ℝ) / 48 := by positivity
  unfold H2
  exact ((((integrable_mom hb1 5).const_mul _).add ((integrable_mom hb1 4).const_mul _)).add
    (integrable_J64.const_mul _)).add
    (((integrable_mom hb2 1).add ((integrable_mom hb2 3).const_mul _)).const_mul _)

theorem H2_bound : ∃ K, ∀ m : ℕ, 4 ≤ m → ∫ t, H2 m t ≤ K / ((m : ℝ) ^ 3 * √m) := by
  obtain ⟨ca, hca⟩ := pow_mul_bound_k 4 (r := 24 / 25) (by norm_num) (by norm_num)
  obtain ⟨cb, hcb⟩ := pow_mul_bound_k 2 (r := Real.exp (-(1 / 48))) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by norm_num))
  have hca0 : 0 ≤ ca := by have := hca 0; simpa using this
  have hcb0 : 0 ≤ cb := by have := hcb 0; simpa using this
  have hc1 : 0 ≤ c1 := by unfold c1; positivity
  have hK := Kε_pos
  have hM1 := Mom_nonneg 1
  have hM3 := Mom_nonneg 3
  have hM4 := Mom_nonneg 4
  have hM5 := Mom_nonneg 5
  set Ka := c1 * Mom 5 * 32 ^ 5 * √32
  set Kb := Kε * Mom 4 * 32 ^ 4 * √32
  set Kc := (25 / 24) ^ 4 * ca * J64
  set Kd := (Mom 1 * 48 * √48 + Mom 3 * 48 ^ 3 * √48 / 2880) * cb
  refine ⟨Ka + Kb + Kc + Kd, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hs : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hmp
  have hsm : √(m : ℝ) ≤ m := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hq : 0 < (m : ℝ) ^ 3 * √m := by positivity
  have h32 : √((m : ℝ) / 32) = √m / √32 := Real.sqrt_div' _ (by norm_num)
  have h48 : √((m : ℝ) / 48) = √m / √48 := Real.sqrt_div' _ (by norm_num)
  have hs32 : 0 < √(32 : ℝ) := by positivity
  have hs48 : 0 < √(48 : ℝ) := by positivity
  rw [integral_H2 hm1]
  have ta : c1 * (m : ℝ) ^ 2 * (Mom 5 / (((m : ℝ) / 32) ^ 5 * √((m : ℝ) / 32))) =
      Ka / ((m : ℝ) ^ 3 * √m) := by
    rw [h32]; simp only [Ka]; field_simp
  have tb : Kε * (m : ℝ) * (Mom 4 / (((m : ℝ) / 32) ^ 4 * √((m : ℝ) / 32))) =
      Kb / ((m : ℝ) ^ 3 * √m) := by
    rw [h32]; simp only [Kb]; field_simp
  have tc : (24 / 25 : ℝ) ^ (m - 4) * J64 ≤ Kc / ((m : ℝ) ^ 3 * √m) := by
    have hpow : (24 / 25 : ℝ) ^ (m - 4) = (25 / 24) ^ 4 * (24 / 25 : ℝ) ^ m := by
      rw [show m = (m - 4) + 4 by omega, pow_add, show m - 4 + 4 - 4 = m - 4 by omega]; ring
    rw [hpow, le_div_iff₀ hq]
    have : (24 / 25 : ℝ) ^ m * ((m : ℝ) ^ 3 * √m) ≤ ca := by
      calc (24 / 25 : ℝ) ^ m * ((m : ℝ) ^ 3 * √m) ≤ (24 / 25 : ℝ) ^ m * ((m : ℝ) ^ 3 * m) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsm (by positivity))
              (by positivity)
        _ = (m : ℝ) ^ 4 * (24 / 25) ^ m := by ring
        _ ≤ ca := hca m
    simp only [Kc]
    have hJ := J64_nonneg
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (by norm_num : (0 : ℝ) ≤ (25 / 24) ^ 4) hJ)
    nlinarith
  have td : Real.exp (-((m : ℝ) / 48)) * (Mom 1 / (((m : ℝ) / 48) ^ 1 * √((m : ℝ) / 48)) +
      (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * √((m : ℝ) / 48)))) ≤
      Kd / ((m : ℝ) ^ 3 * √m) := by
    have he : Real.exp (-((m : ℝ) / 48)) = Real.exp (-(1 / 48)) ^ m := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hbnd : Real.exp (-(1 / 48)) ^ m * (m : ℝ) ^ 2 ≤ cb := by
      have := hcb m; linarith [mul_comm ((m : ℝ) ^ 2) (Real.exp (-(1 / 48)) ^ m)]
    rw [he, h48]
    have hinner : Mom 1 / (((m : ℝ) / 48) ^ 1 * (√m / √48)) +
        (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * (√m / √48))) ≤
        (Mom 1 * 48 * √48 + Mom 3 * 48 ^ 3 * √48 / 2880) / ((m : ℝ) * √m) := by
      have e1 : Mom 1 / (((m : ℝ) / 48) ^ 1 * (√m / √48)) = Mom 1 * 48 * √48 / ((m : ℝ) * √m) := by
        field_simp
      have e2 : (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * (√m / √48))) =
          Mom 3 * 48 ^ 3 * √48 / 2880 / ((m : ℝ) ^ 2 * √m) := by
        field_simp
      rw [e1, e2, add_div]
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ hs.le
      nlinarith
    calc Real.exp (-(1 / 48)) ^ m * (Mom 1 / (((m : ℝ) / 48) ^ 1 * (√m / √48)) +
          (m : ℝ) / 2880 * (Mom 3 / (((m : ℝ) / 48) ^ 3 * (√m / √48))))
        ≤ Real.exp (-(1 / 48)) ^ m *
          ((Mom 1 * 48 * √48 + Mom 3 * 48 ^ 3 * √48 / 2880) / ((m : ℝ) * √m)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (Mom 1 * 48 * √48 + Mom 3 * 48 ^ 3 * √48 / 2880) *
          (Real.exp (-(1 / 48)) ^ m * (m : ℝ) ^ 2) / ((m : ℝ) ^ 3 * √m) := by
          field_simp
      _ ≤ (Mom 1 * 48 * √48 + Mom 3 * 48 ^ 3 * √48 / 2880) * cb / ((m : ℝ) ^ 3 * √m) := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact mul_le_mul_of_nonneg_left hbnd (by positivity)
  rw [ta, tb]
  have := add_le_add (add_le_add (add_le_add (le_refl (Ka / ((m : ℝ) ^ 3 * √m)))
    (le_refl (Kb / ((m : ℝ) ^ 3 * √m)))) tc) td
  refine this.trans (le_of_eq ?_)
  field_simp

/-! ### The second-order expansion of `J_m = ∫ t² r_E^m` -/

/-- `J_m = ∫ t² r_E(t)^m dt`. -/
def Jm (m : ℕ) : ℝ := ∫ t : ℝ, t ^ 2 * rE t ^ m

lemma integrable_t2_rE {m : ℕ} (hm : 4 ≤ m) : Integrable (fun t : ℝ => t ^ 2 * rE t ^ m) := by
  refine integrable_J64.mono' ?_ (Eventually.of_forall (fun t => ?_))
  · exact ((continuous_pow 2).mul
      (EulerianCert.FourierModes.continuous_rE.pow m)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t), abs_pow]
    have h1 : |rE t| ≤ 1 := EulerianCert.EulerianFourier.abs_rE_le_one t
    have hr2 : |rE t| ^ (1 + 1) ≤ 8 * (4 + t ^ 2)⁻¹ :=
      EulerianCert.EulerianFourier.pow_rE_le (n := 1) le_rfl t
    have hr4 : |rE t| ^ 4 ≤ 64 * ((4 + t ^ 2)⁻¹) ^ 2 := by
      rw [show (4 : ℕ) = (1 + 1) * 2 from rfl, pow_mul]
      calc (|rE t| ^ (1 + 1)) ^ 2 ≤ (8 * (4 + t ^ 2)⁻¹) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hr2 2
        _ = 64 * ((4 + t ^ 2)⁻¹) ^ 2 := by ring
    have hm4 : |rE t| ^ m ≤ |rE t| ^ 4 := pow_le_pow_of_le_one (abs_nonneg _) h1 hm
    have h4 : 0 < 4 + t ^ 2 := by positivity
    have hq : t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2 ≤ (4 + t ^ 2)⁻¹ := by
      rw [show t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2 = (t ^ 2 / (4 + t ^ 2)) * (4 + t ^ 2)⁻¹ by field_simp]
      apply mul_le_of_le_one_left (by positivity)
      rw [div_le_one h4]; linarith
    calc t ^ 2 * |rE t| ^ m ≤ t ^ 2 * (64 * ((4 + t ^ 2)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left (hm4.trans hr4) (sq_nonneg t)
      _ = 64 * (t ^ 2 * ((4 + t ^ 2)⁻¹) ^ 2) := by ring
      _ ≤ 64 * (4 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hq (by norm_num)

lemma integral_Main {m : ℕ} (hm : 1 ≤ m) :
    ∫ t, Main m t = √π / 2 * ((24 / (m : ℝ)) * √(24 / (m : ℝ))) * (1 - 3 / (4 * m)) := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb0 : (0 : ℝ) < (m : ℝ) / 24 := by positivity
  unfold Main
  rw [integral_sub (integrable_mom hb0 1) ((integrable_mom hb0 3).const_mul _),
    integral_const_mul, integral_mom hb0, integral_mom hb0, Mom_one, Mom_three]
  have hs : √(24 / (m : ℝ)) = (√((m : ℝ) / 24))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  rw [hs]
  have hsb : 0 < √((m : ℝ) / 24) := Real.sqrt_pos.mpr hb0
  field_simp
  ring

theorem J_asymp : ∃ K, ∀ m : ℕ, 4 ≤ m →
    |Jm m - √π / 2 * ((24 / (m : ℝ)) * √(24 / (m : ℝ))) * (1 - 3 / (4 * m))| ≤
      K / ((m : ℝ) ^ 3 * √m) := by
  obtain ⟨K, hK⟩ := H2_bound
  refine ⟨K, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hb0 : (0 : ℝ) < (m : ℝ) / 24 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    positivity
  have hMi : Integrable (Main m) := by
    unfold Main
    exact (integrable_mom hb0 1).sub ((integrable_mom hb0 3).const_mul _)
  rw [← integral_Main hm1, Jm, ← integral_sub (integrable_t2_rE hm) hMi]
  refine le_trans ?_ (hK m hm)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (integrable_H2 hm1)
  exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact pointwise2 hm t)

/-! ### Eq. (86)–(87): `I_D` and the central slopes -/

lemma one_sub_cos_eq (t : ℝ) : 1 - Real.cos t = t ^ 2 / 2 * rE t ^ 2 := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp
  · rw [EulerianCert.FourierModes.rE_of_ne_zero h]
    have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h2 := Real.sin_sq_add_cos_sq (t / 2)
      have h3 := Real.cos_two_mul (t / 2)
      rw [show 2 * (t / 2) = t by ring] at h3
      linarith
    rw [hc]
    field_simp
    ring

/-- `I_D = ∫ r_E(t)^D (1 − cos t) dt` (Eq. (86)). -/
def ID (D : ℕ) : ℝ := ∫ t : ℝ, rE t ^ D * (1 - Real.cos t)

lemma ID_eq (D : ℕ) : ID D = 1 / 2 * Jm (D + 2) := by
  unfold ID Jm
  rw [← integral_const_mul]
  congr 1; funext t
  rw [one_sub_cos_eq, pow_add]; ring

/-! ### From `m = D + 2` to `D` -/

lemma conv_y {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 2) :
    |(1 - y) * √(1 - y) * (1 - 3 * y / 8) - (1 - 15 * y / (8 * (1 - y)))| ≤ 6 * y ^ 2 := by
  have h1y : 0 < 1 - y := by linarith
  set s := √(1 - y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - y := Real.sq_sqrt h1y.le
  have hsu : s ≤ 1 - y / 2 := by
    rw [hs, Real.sqrt_le_left (by linarith)]; nlinarith
  have hsl : 1 - y / 2 - y ^ 2 / 2 ≤ s := by
    rw [hs, Real.le_sqrt (by nlinarith) h1y.le]; nlinarith [sq_nonneg y, pow_nonneg hy0.le 3]
  set q := 1 / (1 - y) with hq
  have hq1 : q * (1 - y) = 1 := by rw [hq]; field_simp
  have hqe : 15 * y / (8 * (1 - y)) = 15 * y * q / 8 := by rw [hq]; field_simp
  have hqb : q ≤ 2 := by rw [hq, div_le_iff₀ h1y]; linarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqm : q - 1 = y * q := by linarith
  rw [hqe, abs_le]
  have hc : 0 < (1 - y) * (1 - 3 * y / 8) := by nlinarith
  constructor
  · have := mul_le_mul_of_nonneg_left hsl hc.le
    nlinarith [sq_nonneg y, pow_nonneg hy0.le 3, mul_pos hy0 hq0]
  · have := mul_le_mul_of_nonneg_left hsu hc.le
    nlinarith [sq_nonneg y, pow_nonneg hy0.le 3, mul_pos hy0 hq0]

lemma conv_D {D : ℝ} (hD : 2 ≤ D) :
    |(24 / (D + 2)) * √(24 / (D + 2)) * (1 - 3 / (4 * (D + 2))) -
      (24 / D) * √(24 / D) * (1 - 15 / (4 * D))| ≤ 24 * √24 * 24 / (D ^ 3 * √D) := by
  have hDp : 0 < D := by linarith
  set y := 2 / (D + 2) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ (by linarith)]; linarith
  have h1y : 1 - y = D / (D + 2) := by rw [hy]; field_simp; ring
  have hsplit : √(24 / (D + 2)) = √(24 / D) * √(1 - y) := by
    rw [h1y, ← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have e1 : (24 / (D + 2)) = (24 / D) * (1 - y) := by rw [h1y]; field_simp
  have e2 : 3 / (4 * (D + 2)) = 3 * y / 8 := by rw [hy]; field_simp; ring
  have e3 : 15 / (4 * D) = 15 * y / (8 * (1 - y)) := by rw [h1y, hy]; field_simp; ring
  rw [hsplit, e1, e2, e3]
  have hc := conv_y hy0 hy1
  have hfac : 24 / D * (1 - y) * (√(24 / D) * √(1 - y)) * (1 - 3 * y / 8) -
      24 / D * √(24 / D) * (1 - 15 * y / (8 * (1 - y))) =
      (24 / D * √(24 / D)) * ((1 - y) * √(1 - y) * (1 - 3 * y / 8) -
        (1 - 15 * y / (8 * (1 - y)))) := by ring
  rw [hfac, abs_mul, abs_of_pos (by positivity)]
  have hyD : y ^ 2 ≤ 4 / D ^ 2 := by
    rw [hy, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hsq : √(24 / D) = √24 / √D := Real.sqrt_div' _ hDp.le
  have hsD : 0 < √D := Real.sqrt_pos.mpr hDp
  calc 24 / D * √(24 / D) * |(1 - y) * √(1 - y) * (1 - 3 * y / 8) -
        (1 - 15 * y / (8 * (1 - y)))| ≤ 24 / D * √(24 / D) * (6 * (4 / D ^ 2)) :=
        mul_le_mul_of_nonneg_left (hc.trans (by linarith)) (by positivity)
    _ = 24 * √24 * 24 / (D ^ 3 * √D) := by rw [hsq]; field_simp; ring

/-! ### Eqs. (91), (92), (85) -/

/-- **Eq. (91)**: `I_D = (√π/4)(24/D)^{3/2}(1 − 15/(4D) + O(D^{−2}))`, in the form
`|I_D − (√π/4)(24/D)√(24/D)(1 − 15/(4D))| ≤ K D^{−7/2}` for all `D ≥ 2`. -/
theorem ID_asymp : ∃ K, ∀ D : ℕ, 2 ≤ D →
    |ID D - √π / 4 * ((24 / (D : ℝ)) * √(24 / (D : ℝ))) * (1 - 15 / (4 * D))| ≤
      K / ((D : ℝ) ^ 3 * √D) := by
  obtain ⟨K, hK⟩ := J_asymp
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 4 le_rfl); 
    have hp : (0 : ℝ) < ((4 : ℕ) : ℝ) ^ 3 * √((4 : ℕ) : ℝ) := by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hp))
  refine ⟨K / 2 + √π / 4 * (24 * √24 * 24), fun D hD => ?_⟩
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0 : ℝ) < D := by linarith
  have hq : 0 < (D : ℝ) ^ 3 * √D := by positivity
  have hJ := hK (D + 2) (by omega)
  have hconv := conv_D hDr
  push_cast at hJ hconv
  have hmono : K / (((D : ℝ) + 2) ^ 3 * √((D : ℝ) + 2)) ≤ K / ((D : ℝ) ^ 3 * √D) := by
    apply div_le_div_of_nonneg_left hK0 hq
    exact mul_le_mul (pow_le_pow_left₀ hDp.le (by linarith) 3)
      (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)
  rw [ID_eq]
  push_cast
  have hdecomp : 1 / 2 * Jm (D + 2) - √π / 4 * (24 / (D : ℝ) * √(24 / (D : ℝ))) * (1 - 15 / (4 * D)) =
      1 / 2 * (Jm (D + 2) - √π / 2 * (24 / ((D : ℝ) + 2) * √(24 / ((D : ℝ) + 2))) *
        (1 - 3 / (4 * ((D : ℝ) + 2)))) +
      √π / 4 * ((24 / ((D : ℝ) + 2)) * √(24 / ((D : ℝ) + 2)) * (1 - 3 / (4 * ((D : ℝ) + 2))) -
        (24 / (D : ℝ)) * √(24 / (D : ℝ)) * (1 - 15 / (4 * D))) := by ring
  rw [hdecomp]
  have hπ : 0 ≤ √π / 4 := by positivity
  calc |1 / 2 * (Jm (D + 2) - √π / 2 * (24 / ((D : ℝ) + 2) * √(24 / ((D : ℝ) + 2))) *
        (1 - 3 / (4 * ((D : ℝ) + 2)))) +
      √π / 4 * ((24 / ((D : ℝ) + 2)) * √(24 / ((D : ℝ) + 2)) * (1 - 3 / (4 * ((D : ℝ) + 2))) -
        (24 / (D : ℝ)) * √(24 / (D : ℝ)) * (1 - 15 / (4 * D)))|
      ≤ 1 / 2 * (K / ((D : ℝ) ^ 3 * √D)) + √π / 4 * (24 * √24 * 24 / ((D : ℝ) ^ 3 * √D)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left (hJ.trans hmono) (by norm_num)
        · rw [abs_mul, abs_of_nonneg hπ]
          exact mul_le_mul_of_nonneg_left hconv hπ
    _ = (K / 2 + √π / 4 * (24 * √24 * 24)) / ((D : ℝ) ^ 3 * √D) := by field_simp

/-- `(D/2π)(√π/4)(24/D)√(24/D) = √(216/(πD))`. -/
lemma slope_const {D : ℝ} (hD : 0 < D) :
    D / (2 * π) * (√π / 4 * ((24 / D) * √(24 / D))) = √(216 / (π * D)) := by
  have hpi := Real.pi_pos
  have h1 : √(216 / (π * D)) = 3 / √π * √(24 / D) := by
    rw [show 216 / (π * D) = (9 / π) * (24 / D) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_div' _ hpi.le,
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1]
  have hsp : 0 < √π := Real.sqrt_pos.mpr hpi
  have hss : √π * √π = π := Real.mul_self_sqrt hpi.le
  have hc : D / (2 * π) * (√π / 4 * (24 / D)) = 3 / √π := by
    rw [eq_div_iff hsp.ne']
    field_simp
    nlinarith [hss]
  calc D / (2 * π) * (√π / 4 * ((24 / D) * √(24 / D)))
      = (D / (2 * π) * (√π / 4 * (24 / D))) * √(24 / D) := by ring
    _ = 3 / √π * √(24 / D) := by rw [hc]

/-- The central slope `s_n = (n+1)(p_{n,(n+1)/2} − p_{n,(n−1)/2})` for `n = 2j + 1`. -/
def slope (j : ℕ) : ℝ :=
  ((2 * j + 1 : ℕ) + 1 : ℝ) * ((EulerianCert.Bracket.E (2 * j + 1) j : ℝ) / (2 * j + 1).factorial -
    (EulerianCert.Bracket.E (2 * j + 1) (j - 1) : ℝ) / (2 * j + 1).factorial)

lemma slope_eq {j : ℕ} (hj : 1 ≤ j) :
    slope j = ((2 * j + 2 : ℕ) : ℝ) / (2 * π) * ID (2 * j + 2) := by
  unfold slope ID
  rw [EulerianCert.EulerianFourier.central_slope_integral hj]
  push_cast; ring_nf

/-- **Eq. (92)**: `s_n = √(216/(πD)) (1 − 15/(4D) + O(D^{−2}))`, `D = n + 1`, `n = 2j + 1`:
`|s_n − √(216/(πD))(1 − 15/(4D))| ≤ K D^{−5/2}`. -/
theorem slope_asymp : ∃ K, ∀ j : ℕ, 1 ≤ j →
    |slope j - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) * (1 - 15 / (4 * ((2 * j + 2 : ℕ) : ℝ)))| ≤
      K / (((2 * j + 2 : ℕ) : ℝ) ^ 2 * √((2 * j + 2 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := ID_asymp
  refine ⟨K / (2 * π), fun j hj => ?_⟩
  set D := 2 * j + 2
  have hD : 2 ≤ D := by omega
  have hDp : (0 : ℝ) < D := by have : (2 : ℝ) ≤ D := by exact_mod_cast hD
                               linarith
  rw [slope_eq hj, ← slope_const hDp]
  have hb := hK D hD
  rw [show (D : ℝ) / (2 * π) * ID D - D / (2 * π) * (√π / 4 * (24 / (D : ℝ) * √(24 / (D : ℝ)))) *
      (1 - 15 / (4 * (D : ℝ))) = D / (2 * π) * (ID D - √π / 4 * (24 / (D : ℝ) * √(24 / (D : ℝ))) *
      (1 - 15 / (4 * (D : ℝ)))) by ring, abs_mul, abs_of_pos (by positivity)]
  calc (D : ℝ) / (2 * π) * |ID D - √π / 4 * (24 / (D : ℝ) * √(24 / (D : ℝ))) *
        (1 - 15 / (4 * (D : ℝ)))| ≤ D / (2 * π) * (K / ((D : ℝ) ^ 3 * √D)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K / (2 * π) / ((D : ℝ) ^ 2 * √D) := by field_simp

/-- **Eq. (85)**: `c_n = 1/s_n = √(π(n+1)/216) (1 + 15/(4(n+1)) + O(n^{−2}))`:
for all large `n = 2j + 1`, `|c_n − √(πD/216)(1 + 15/(4D))| ≤ K D^{−3/2}`. -/
theorem inverse_slope_asymp : ∃ K, ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
    |1 / slope j - √(π * ((2 * j + 2 : ℕ) : ℝ) / 216) * (1 + 15 / (4 * ((2 * j + 2 : ℕ) : ℝ)))| ≤
      K / (((2 * j + 2 : ℕ) : ℝ) * √((2 * j + 2 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := slope_asymp
  set K2 := |K| * √(π / 216)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * K2 + 15)
  refine ⟨√(π / 216) * 2 * (225 / 16 + 2 * K2), N0 + 1, fun j hj => ?_⟩
  have hj1 : 1 ≤ j := by omega
  set D := 2 * j + 2
  have hDr : (N0 : ℝ) + 1 ≤ (D : ℝ) := by
    have : N0 + 1 ≤ D := by omega
    exact_mod_cast this
  have hDp : (0 : ℝ) < D := by linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  have hD1 : (1 : ℝ) ≤ D := by linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  have hDbig : 4 * K2 + 15 < (D : ℝ) := by linarith
  have hK2 : 0 ≤ K2 := by positivity
  set σ := √(216 / (π * (D : ℝ)))
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσinv : 1 / σ = √(π * (D : ℝ) / 216) := by
    simp only [σ]; rw [one_div, ← Real.sqrt_inv, inv_div]
  set a := 15 / (4 * (D : ℝ))
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 1 / 4 := by
    simp only [a]; rw [div_le_iff₀ (by positivity)]; linarith
  set s := slope j
  set ε := (s - σ * (1 - a)) / σ
  have hsε : s = σ * (1 - a + ε) := by simp only [ε]; field_simp; ring
  have hsD : 0 < √(D : ℝ) := Real.sqrt_pos.mpr hDp
  have hε : |ε| ≤ K2 / (D : ℝ) ^ 2 := by
    have hb := hK j hj1
    simp only [ε]
    rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    refine hb.trans ?_
    have hσD : σ = √216 / (√π * √(D : ℝ)) := by
      simp only [σ]; rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity)]
    have hK2' : K2 = |K| * (√π / √216) := by
      simp only [K2]; rw [Real.sqrt_div' _ (by norm_num)]
    rw [hσD, hK2']
    have hs216 : 0 < √(216 : ℝ) := by positivity
    have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    rw [show |K| * (√π / √216) / (D : ℝ) ^ 2 * (√216 / (√π * √(D : ℝ))) =
      |K| / ((D : ℝ) ^ 2 * √(D : ℝ)) by field_simp]
    exact div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
  have hεs : |ε| ≤ 1 / 4 := by
    refine hε.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hden : 1 / 2 ≤ 1 - a + ε := by
    have := neg_abs_le ε; linarith
  have hspos : 0 < s := by rw [hsε]; exact mul_pos hσ (by linarith)
  have hkey : 1 / s - √(π * (D : ℝ) / 216) * (1 + a) =
      (1 / σ) * ((a ^ 2 - ε * (1 + a)) / (1 - a + ε)) := by
    rw [← hσinv, hsε]; field_simp; ring
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / σ), abs_div,
    abs_of_pos (show (0 : ℝ) < 1 - a + ε by linarith), hσinv]
  have hnum : |a ^ 2 - ε * (1 + a)| ≤ (225 / 16 + 2 * K2) / (D : ℝ) ^ 2 := by
    have ha2 : a ^ 2 = 225 / 16 / (D : ℝ) ^ 2 := by simp only [a]; field_simp; ring
    calc |a ^ 2 - ε * (1 + a)| ≤ |a ^ 2| + |ε * (1 + a)| := abs_sub _ _
      _ = a ^ 2 + |ε| * (1 + a) := by
          rw [abs_of_nonneg (sq_nonneg a), abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + a)]
      _ ≤ 225 / 16 / (D : ℝ) ^ 2 + K2 / (D : ℝ) ^ 2 * 2 := by
          rw [ha2]; exact add_le_add le_rfl (mul_le_mul hε (by linarith) (by linarith)
            (by positivity))
      _ = (225 / 16 + 2 * K2) / (D : ℝ) ^ 2 := by ring
  have hsqD : √(π * (D : ℝ) / 216) = √(π / 216) * √(D : ℝ) := by
    rw [show π * (D : ℝ) / 216 = (π / 216) * D by ring, Real.sqrt_mul (by positivity)]
  rw [hsqD]
  calc √(π / 216) * √(D : ℝ) * (|a ^ 2 - ε * (1 + a)| / (1 - a + ε))
      ≤ √(π / 216) * √(D : ℝ) * (((225 / 16 + 2 * K2) / (D : ℝ) ^ 2) / (1 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ = √(π / 216) * 2 * (225 / 16 + 2 * K2) / ((D : ℝ) * √(D : ℝ)) := by
        have hss : √(D : ℝ) * √(D : ℝ) = D := Real.mul_self_sqrt hDp.le
        field_simp
        nlinarith [hss]

end EulerianCert.CentralSlope
