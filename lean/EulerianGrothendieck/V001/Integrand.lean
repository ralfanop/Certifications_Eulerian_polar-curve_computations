import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Manuscript 11, proof of Lemma 3.15: Eqs. (89)–(90) verbatim

`r_E(t) = sinc(t/2) = 2 sin(t/2)/t`, `D ≥ 1`, `δ = D^{−2/5}`.  For `|t| ≤ δ`, uniformly,

* **(89)** `r_E(t)^D (1 − cos t) = e^{−Dt²/24} (t²/2 − t⁴/24 − Dt⁶/5760 + R)`,
* **(90)** `R = O(t⁶ + Dt⁸ + D²t¹⁰)`.

Here `R` is defined by (89) itself (`remainder`), and (90) is the theorem `remainder_bound`:
there is an absolute constant `K` with `|R| ≤ K (t⁶ + D t⁸ + D² t¹⁰)` for every `D ≥ 1` and
every `|t| ≤ D^{−2/5}`.  The proof follows the manuscript: `log r_E(t) = −t²/24 − t⁴/2880 + O(t⁶)`
(as two-sided exponential bounds with the explicit constant `10⁻⁴`) and
`1 − cos t = t²/2 − t⁴/24 + O(t⁶)`, together with `D t⁴ ≤ D^{−3/5} ≤ 1`.

Self-contained module (Lean 4.24, Mathlib of the EulerianGrothendieck project); the elementary
Taylor bounds are those of `EulerianCert.LocalLimit` and `EulerianCert.CentralSlope`.
-/

open Real

noncomputable section

namespace V001Cert

/-- The Eulerian radial profile `r_E(t) = sin(t/2)/(t/2)`, `r_E(0) = 1`. -/
def rE (t : ℝ) : ℝ := Real.sinc (t / 2)

lemma rE_zero : rE 0 = 1 := by simp [rE]

lemma rE_neg (t : ℝ) : rE (-t) = rE t := by
  simp only [rE, neg_div, Real.sinc_neg]

lemma rE_of_ne_zero {t : ℝ} (ht : t ≠ 0) : rE t = 2 * Real.sin (t / 2) / t := by
  rw [rE, Real.sinc_of_ne_zero (by positivity : t / 2 ≠ 0)]
  field_simp

/-! ### Taylor inequalities -/

/-- `f(0) = 0` and `f' ≥ 0` on `[0, ∞)` give `f ≥ 0` on `[0, ∞)`. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Ici] at hy
    rw [(hf y).deriv]
    exact hd y (le_of_lt hy)
  have := hmono Set.left_mem_Ici hx hx
  rwa [h0] at this

lemma sin_ge {y : ℝ} (hy : 0 ≤ y) : y - y ^ 3 / 6 ≤ Real.sin y := by
  have := nonneg_of_deriv_nonneg (f := fun y => Real.sin y - y + y ^ 3 / 6)
    (f' := fun y => Real.cos y - 1 + y ^ 2 / 2)
    (fun x => by
      have := ((hasDerivAt_sin x).sub (hasDerivAt_id' x)).add ((hasDerivAt_pow 3 x).div_const 6)
      convert this using 1; push_cast; ring)
    (by simp) (fun x _ => by have := one_sub_sq_div_two_le_cos (x := x); linarith) hy
  linarith

lemma cos_le {y : ℝ} (hy : 0 ≤ y) : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
  have := nonneg_of_deriv_nonneg (f := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    (f' := fun y => -y + y ^ 3 / 6 + Real.sin y)
    (fun x => by
      have := ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub (hasDerivAt_cos x))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := sin_ge hx; linarith) hy
  linarith

lemma sin_le {y : ℝ} (hy : 0 ≤ y) : Real.sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
  have := nonneg_of_deriv_nonneg (f := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y)
    (f' := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    (fun x => by
      have := ((((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub (hasDerivAt_sin x))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := cos_le hx; linarith) hy
  linarith

lemma cos_ge {y : ℝ} (hy : 0 ≤ y) : 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 ≤ Real.cos y := by
  have := nonneg_of_deriv_nonneg (f := fun y => Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720)
    (f' := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y)
    (fun x => by
      have := (((((hasDerivAt_cos x).sub (hasDerivAt_const x (1 : ℝ))).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 4 x).div_const 24)).add
        ((hasDerivAt_pow 6 x).div_const 720))
      convert this using 1; push_cast; ring)
    (by simp) (fun x hx => by have := sin_le hx; linarith) hy
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

/-- `1 − cos t = t²/2 − t⁴/24 + c` with `0 ≤ c ≤ t⁶/720`, for every real `t`. -/
lemma one_sub_cos_bounds (t : ℝ) :
    t ^ 2 / 2 - t ^ 4 / 24 ≤ 1 - Real.cos t ∧
      1 - Real.cos t ≤ t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 := by
  have hc : Real.cos t = Real.cos |t| := (Real.cos_abs t).symm
  have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
  have h6 : |t| ^ 6 = t ^ 6 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2, ← pow_mul]
  have a := cos_le (abs_nonneg t)
  have b := cos_ge (abs_nonneg t)
  rw [h2, h4] at a
  rw [h2, h4, h6] at b
  constructor <;> linarith

lemma one_sub_cos_le (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have := one_sub_sq_div_two_le_cos (x := t); linarith

/-! ### Bounds for `r_E` -/

lemma rE_eq_abs (t : ℝ) (ht : t ≠ 0) : rE t = Real.sin (|t| / 2) / (|t| / 2) := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [← rE_neg, rE_of_ne_zero (by linarith), abs_of_neg h]
    field_simp
  · rw [rE_of_ne_zero ht, abs_of_pos h]; field_simp

lemma rE_le (t : ℝ) : rE t ≤ 1 - t ^ 2 / 24 + t ^ 4 / 1920 := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [rE_zero]
  · rw [rE_eq_abs t h]
    have hy : 0 < |t| / 2 := by positivity
    rw [div_le_iff₀ hy]
    have := sin_le hy.le
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
    nlinarith

lemma rE_ge6 (t : ℝ) : 1 - t ^ 2 / 24 + t ^ 4 / 1920 - t ^ 6 / 322560 ≤ rE t := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [rE_zero]
  · rw [rE_eq_abs t h]
    have hy : 0 < |t| / 2 := by positivity
    rw [le_div_iff₀ hy]
    have := sin_ge7 hy.le
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul]
    have h6 : |t| ^ 6 = t ^ 6 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2, ← pow_mul]
    nlinarith

lemma rE_nonneg {t : ℝ} (ht : |t| ≤ 2 * π) : 0 ≤ rE t := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [rE_zero]
  · rw [rE_eq_abs t h]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith))
      (by positivity)

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

/-! ### `r_E(t) = exp(−t²/24 − t⁴/2880 + ε)`, `|ε| ≤ t⁶/10⁴` on `|t| ≤ 1` -/

/-- The constant `10⁻⁴` of the sixth-order error of `log r_E`. -/
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

/-! ### Eqs. (89)–(90) -/

/-- The remainder `R` of Eq. (89), defined by that equation. -/
def remainder (D : ℕ) (t : ℝ) : ℝ :=
  rE t ^ D * (1 - Real.cos t) * Real.exp ((D : ℝ) * t ^ 2 / 24)
    - (t ^ 2 / 2 - t ^ 4 / 24 - (D : ℝ) * t ^ 6 / 5760)

/-- **Eq. (89)**: `r_E(t)^D (1 − cos t) = e^{−Dt²/24}(t²/2 − t⁴/24 − Dt⁶/5760 + R)`. -/
theorem integrand_eq (D : ℕ) (t : ℝ) :
    rE t ^ D * (1 - Real.cos t) =
      Real.exp (-((D : ℝ) * t ^ 2 / 24)) *
        (t ^ 2 / 2 - t ^ 4 / 24 - (D : ℝ) * t ^ 6 / 5760 + remainder D t) := by
  have h : Real.exp ((D : ℝ) * t ^ 2 / 24) * Real.exp (-((D : ℝ) * t ^ 2 / 24)) = 1 := by
    rw [← Real.exp_add]; simp
  calc rE t ^ D * (1 - Real.cos t)
      = rE t ^ D * (1 - Real.cos t) *
          (Real.exp ((D : ℝ) * t ^ 2 / 24) * Real.exp (-((D : ℝ) * t ^ 2 / 24))) := by
        rw [h, mul_one]
    _ = _ := by unfold remainder; ring

/-- If `e^{a−B} ≤ X ≤ e^{a+B}`, `B ≥ 0` and `|a| + B ≤ 1`, then
`|X − 1 − a| ≤ e (2a² + 2B²) + B`. -/
lemma sandwich {X a B : ℝ} (hB : 0 ≤ B) (h1 : Real.exp (a - B) ≤ X) (h2 : X ≤ Real.exp (a + B))
    (hab : |a| + B ≤ 1) :
    |X - 1 - a| ≤ Real.exp 1 * (2 * a ^ 2 + 2 * B ^ 2) + B := by
  have key : ∀ z : ℝ, |z| ≤ 1 → |Real.exp z - 1 - z| ≤ Real.exp 1 * z ^ 2 := by
    intro z hz
    refine (abs_exp_sub_one_sub z).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz) (sq_nonneg z)
  have hp : |a + B| ≤ 1 := (abs_add_le a B).trans (by rw [abs_of_nonneg hB]; exact hab)
  have hm : |a - B| ≤ 1 := (abs_sub a B).trans (by rw [abs_of_nonneg hB]; exact hab)
  have kp := abs_le.mp (key _ hp)
  have km := abs_le.mp (key _ hm)
  have sp : (a + B) ^ 2 ≤ 2 * a ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (a - B)]
  have sm : (a - B) ^ 2 ≤ 2 * a ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (a + B)]
  have e1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have tp := mul_le_mul_of_nonneg_left sp e1
  have tm := mul_le_mul_of_nonneg_left sm e1
  rw [abs_le]
  constructor <;> nlinarith

/-- `D ≥ 1` and `|t| ≤ D^{−2/5}` give `|t| ≤ 1` and `D t⁴ ≤ 1` (indeed `D t⁴ ≤ D^{−3/5}`). -/
lemma small {D : ℕ} (hD : 1 ≤ D) {t : ℝ} (ht : |t| ≤ (D : ℝ) ^ (-(2 / 5 : ℝ))) :
    |t| ≤ 1 ∧ (D : ℝ) * t ^ 4 ≤ 1 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ D := by linarith
  set δ := (D : ℝ) ^ (-(2 / 5 : ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hD0 _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD1 (by norm_num)
  refine ⟨ht.trans hδ1, ?_⟩
  -- `δ⁵ D² = 1`
  have h5 : δ ^ 5 * (D : ℝ) ^ 2 = 1 := by
    have e : δ ^ 5 = (D : ℝ) ^ (-(2 : ℝ)) := by
      rw [hδ, ← Real.rpow_natCast, ← Real.rpow_mul hD0]; norm_num
    rw [e, Real.rpow_neg hD0, Real.rpow_two]
    have : (D : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  have ht4 : t ^ 4 ≤ δ ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg t) ht 4
    rwa [show |t| ^ 4 = t ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at this
  -- `(D δ⁴)⁵ = D⁵ δ²⁰ = D⁻³ ≤ 1`, hence `D δ⁴ ≤ 1`
  have hx0 : 0 ≤ (D : ℝ) * δ ^ 4 := by positivity
  have hx5 : ((D : ℝ) * δ ^ 4) ^ 5 ≤ 1 := by
    have e : ((D : ℝ) * δ ^ 4) ^ 5 * (D : ℝ) ^ 3 = 1 := by
      have : ((D : ℝ) * δ ^ 4) ^ 5 * (D : ℝ) ^ 3 = (δ ^ 5 * (D : ℝ) ^ 2) ^ 4 := by ring
      rw [this, h5, one_pow]
    have hD3 : 1 ≤ (D : ℝ) ^ 3 := one_le_pow₀ hD1
    nlinarith [pow_nonneg hx0 5]
  have hx1 : (D : ℝ) * δ ^ 4 ≤ 1 := by
    by_contra h
    push_neg at h
    have := one_lt_pow₀ h (by norm_num : (5 : ℕ) ≠ 0)
    linarith
  calc (D : ℝ) * t ^ 4 ≤ (D : ℝ) * δ ^ 4 := mul_le_mul_of_nonneg_left ht4 hD0
    _ ≤ 1 := hx1

set_option maxHeartbeats 1600000 in
/-- **Eq. (90)**: there is an absolute constant `K` such that, for every `D ≥ 1` and every
`|t| ≤ D^{−2/5}`, the remainder of (89) satisfies `|R| ≤ K (t⁶ + D t⁸ + D² t¹⁰)`. -/
theorem remainder_bound :
    ∃ K : ℝ, ∀ D : ℕ, 1 ≤ D → ∀ t : ℝ, |t| ≤ (D : ℝ) ^ (-(2 / 5 : ℝ)) →
      |remainder D t| ≤ K * (t ^ 6 + (D : ℝ) * t ^ 8 + (D : ℝ) ^ 2 * t ^ 10) := by
  refine ⟨3 + 2 * Real.exp 1, fun D hD t ht => ?_⟩
  obtain ⟨ht1, hDt⟩ := small hD ht
  set P : ℝ := (D : ℝ) with hP
  have hP1 : (1 : ℝ) ≤ P := by rw [hP]; exact_mod_cast hD
  set s := t ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg t
  have hs1 : s ≤ 1 := by
    have := sq_le_sq' (abs_le.mp ht1).1 (abs_le.mp ht1).2; simpa [hs] using this
  have e4 : t ^ 4 = s ^ 2 := by rw [hs]; ring
  have e6 : t ^ 6 = s ^ 3 := by rw [hs]; ring
  have e8 : t ^ 8 = s ^ 4 := by rw [hs]; ring
  have e10 : t ^ 10 = s ^ 5 := by rw [hs]; ring
  have hPs : P * s ^ 2 ≤ 1 := by rw [← e4]; exact hDt
  -- the sandwich for `X = r_E^D e^{Dt²/24}`
  set a : ℝ := -(P * s ^ 2 / 2880) with ha
  set B : ℝ := P * Kε * s ^ 3 with hB
  have hKε : (0 : ℝ) < Kε := by unfold Kε; norm_num
  have hB0 : 0 ≤ B := by positivity
  set X := rE t ^ D * Real.exp (P * s / 24) with hX
  have hlow : Real.exp (a - B) ≤ X := by
    have h := pow_le_pow_left₀ (Real.exp_pos _).le (rE_lower6 ht1) D
    rw [← Real.exp_nat_mul] at h
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (P * s / 24)).le
    rw [← Real.exp_add] at this
    refine le_trans (le_of_eq ?_) this
    congr 1; rw [ha, hB, ← hP, e4, e6]; ring
  have hupp : X ≤ Real.exp (a + B) := by
    have h := pow_le_pow_left₀ (le_trans (Real.exp_pos _).le (rE_lower6 ht1)) (rE_upper6 ht1) D
    rw [← Real.exp_nat_mul] at h
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (P * s / 24)).le
    rw [← Real.exp_add] at this
    refine le_trans this (le_of_eq ?_)
    congr 1; rw [ha, hB, ← hP, e4, e6]; ring
  have habs : |a| + B ≤ 1 := by
    rw [ha, abs_neg, abs_of_nonneg (by positivity), hB]
    have h3 : P * s ^ 3 ≤ 1 := by nlinarith
    have hKv : Kε = 1 / 10000 := rfl
    have h4 : P * Kε * s ^ 3 ≤ Kε := by
      calc P * Kε * s ^ 3 = Kε * (P * s ^ 3) := by ring
        _ ≤ Kε * 1 := mul_le_mul_of_nonneg_left h3 hKε.le
        _ = Kε := mul_one _
    rw [hKv] at h4 ⊢
    linarith
  have he := sandwich hB0 hlow hupp habs
  -- `1 − cos t = s/2 − s²/24 + c₆` with `0 ≤ c₆ ≤ s³/720`
  obtain ⟨hc1, hc2⟩ := one_sub_cos_bounds t
  rw [← hs, e4] at hc1
  rw [← hs, e4, e6] at hc2
  set c := 1 - Real.cos t with hc
  have hcle : c ≤ s / 2 := by rw [hc, hs]; exact one_sub_cos_le t
  have hc0 : 0 ≤ c := by rw [hc]; linarith [Real.cos_le_one t]
  set c6 := c - (s / 2 - s ^ 2 / 24) with hc6
  have hc60 : 0 ≤ c6 := by rw [hc6]; linarith
  have hc61 : c6 ≤ s ^ 3 / 720 := by rw [hc6]; linarith
  set e := X - 1 - a with he_def
  -- the exact form of `R`
  have hR : remainder D t = c6 + P * s ^ 4 / 69120 - P * s ^ 2 / 2880 * c6 + e * c := by
    have : remainder D t = X * c - (s / 2 - s ^ 2 / 24 - P * s ^ 3 / 5760) := by
      unfold remainder; rw [hX, hc, ← hP, ← hs, e4, e6]; ring
    rw [this, he_def, hc6, ha]; ring
  -- bounds on the four pieces
  have hE : |e| * c ≤ (Real.exp 1 * (2 * a ^ 2 + 2 * B ^ 2) + B) * (s / 2) :=
    mul_le_mul he hcle hc0 (by positivity)
  have ha2 : a ^ 2 = P ^ 2 * s ^ 4 / 2880 ^ 2 := by rw [ha]; ring
  have hB2 : B ^ 2 = P ^ 2 * Kε ^ 2 * s ^ 6 := by rw [hB]; ring
  have hR1 : |remainder D t| ≤
      s ^ 3 / 720 + P * s ^ 4 / 69120 + P * s ^ 2 / 2880 * (s ^ 3 / 720) +
        (Real.exp 1 * (2 * a ^ 2 + 2 * B ^ 2) + B) * (s / 2) := by
    rw [hR]
    have t1 : |c6| ≤ s ^ 3 / 720 := by rw [abs_of_nonneg hc60]; exact hc61
    have t3 : |P * s ^ 2 / 2880 * c6| ≤ P * s ^ 2 / 2880 * (s ^ 3 / 720) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ P * s ^ 2 / 2880)]
      exact mul_le_mul_of_nonneg_left t1 (by positivity)
    have t4 : |e * c| ≤ (Real.exp 1 * (2 * a ^ 2 + 2 * B ^ 2) + B) * (s / 2) := by
      rw [abs_mul, abs_of_nonneg hc0]; exact hE
    have t2 : |P * s ^ 4 / 69120| = P * s ^ 4 / 69120 := abs_of_nonneg (by positivity)
    calc |c6 + P * s ^ 4 / 69120 - P * s ^ 2 / 2880 * c6 + e * c|
        ≤ |c6| + |P * s ^ 4 / 69120| + |P * s ^ 2 / 2880 * c6| + |e * c| := by
          have := abs_add_le (c6 + P * s ^ 4 / 69120 - P * s ^ 2 / 2880 * c6) (e * c)
          have h2 := abs_sub (c6 + P * s ^ 4 / 69120) (P * s ^ 2 / 2880 * c6)
          have h3 := abs_add_le c6 (P * s ^ 4 / 69120)
          linarith
      _ ≤ _ := by rw [t2]; linarith
  -- comparison with `s³ + P s⁴ + P² s⁵`
  have s4 : s ^ 4 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have s5 : s ^ 5 ≤ s ^ 4 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have s7 : s ^ 7 ≤ s ^ 5 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have hP0 : 0 ≤ P := by linarith
  have hexp : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have T1 : P * s ^ 2 / 2880 * (s ^ 3 / 720) ≤ P * s ^ 4 := by
    have : P * s ^ 5 ≤ P * s ^ 4 := mul_le_mul_of_nonneg_left s5 hP0
    nlinarith [pow_nonneg hs0 5]
  have T2 : (Real.exp 1 * (2 * a ^ 2 + 2 * B ^ 2) + B) * (s / 2) ≤
      2 * Real.exp 1 * (P ^ 2 * s ^ 5) + P * s ^ 4 := by
    rw [ha2, hB2]
    have hK1 : Kε ^ 2 ≤ 1 := by unfold Kε; norm_num
    have u1 : P ^ 2 * s ^ 4 / 2880 ^ 2 * s ≤ P ^ 2 * s ^ 5 := by
      have : P ^ 2 * s ^ 4 / 2880 ^ 2 * s = P ^ 2 * s ^ 5 / 2880 ^ 2 := by ring
      rw [this]; have : 0 ≤ P ^ 2 * s ^ 5 := by positivity
      linarith [show P ^ 2 * s ^ 5 / 2880 ^ 2 ≤ P ^ 2 * s ^ 5 from by
        apply div_le_self this; norm_num]
    have u2 : P ^ 2 * Kε ^ 2 * s ^ 6 * s ≤ P ^ 2 * s ^ 5 := by
      have : P ^ 2 * Kε ^ 2 * s ^ 6 * s = Kε ^ 2 * (P ^ 2 * s ^ 7) := by ring
      rw [this]
      have : P ^ 2 * s ^ 7 ≤ P ^ 2 * s ^ 5 := mul_le_mul_of_nonneg_left s7 (by positivity)
      have : 0 ≤ P ^ 2 * s ^ 7 := by positivity
      nlinarith
    have u3 : P * Kε * s ^ 3 * (s / 2) ≤ P * s ^ 4 := by
      have : P * Kε * s ^ 3 * (s / 2) = Kε / 2 * (P * s ^ 4) := by ring
      rw [this]
      have : 0 ≤ P * s ^ 4 := by positivity
      have : Kε / 2 ≤ 1 := by unfold Kε; norm_num
      nlinarith
    have : (Real.exp 1 * (2 * (P ^ 2 * s ^ 4 / 2880 ^ 2) + 2 * (P ^ 2 * Kε ^ 2 * s ^ 6)) +
        P * Kε * s ^ 3) * (s / 2) =
        Real.exp 1 * (P ^ 2 * s ^ 4 / 2880 ^ 2 * s + P ^ 2 * Kε ^ 2 * s ^ 6 * s) +
          P * Kε * s ^ 3 * (s / 2) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left (add_le_add u1 u2) hexp
    nlinarith
  have T0 : P * s ^ 4 / 69120 ≤ P * s ^ 4 := by
    have : 0 ≤ P * s ^ 4 := by positivity
    linarith [show P * s ^ 4 / 69120 ≤ P * s ^ 4 from div_le_self this (by norm_num)]
  rw [e6, e8, e10]
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  have hPs4 : 0 ≤ P * s ^ 4 := by positivity
  have hPs5 : 0 ≤ P ^ 2 * s ^ 5 := by positivity
  have hsum : |remainder D t| ≤ s ^ 3 + 3 * (P * s ^ 4) + 2 * Real.exp 1 * (P ^ 2 * s ^ 5) := by
    linarith
  have m1 := mul_nonneg hexp hs3
  have m2 := mul_nonneg hexp hPs4
  have expand : (3 + 2 * Real.exp 1) * (s ^ 3 + P * s ^ 4 + P ^ 2 * s ^ 5) =
      3 * s ^ 3 + 3 * (P * s ^ 4) + 3 * (P ^ 2 * s ^ 5) + 2 * (Real.exp 1 * s ^ 3) +
        2 * (Real.exp 1 * (P * s ^ 4)) + 2 * Real.exp 1 * (P ^ 2 * s ^ 5) := by ring
  rw [expand]
  linarith

end V001Cert
