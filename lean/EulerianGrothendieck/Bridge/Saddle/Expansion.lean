import Bridge.Saddle.LogA
import Bridge.Saddle.Gauss

/-!
# Lemma 5.5, part 8: the pointwise expansion (76) of `χ^M` in the inner region

With `u = εz`, `ε = M^{-1/2}`, `b_n = κ_n (iz)^n / n!` and
`T = 1 + εb₃ + ε²(b₄ + b₃²/2) + ε³(b₅ + b₃b₄ + b₃³/6)
      + ε⁴(b₆ + b₃b₅ + b₄²/2 + b₃²b₄/2 + b₃⁴/24)`,
we prove (`inner_pointwise`), uniformly for `|s| ≤ σ` and `ε|z| ≤ δ`,
`|χ(s, εz)^M - e^{-κ₂z²/2} T| ≤ C ε⁵ (1+z²)^{24} e^{-c₀z²/4}`.
This is the expansion (76) carried to fourth order with a fifth-order remainder, which is what
the two-derivative statement needs.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-! ## Algebra -/

theorem norm_pow_succ_sub_pow_le {x y : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ∀ m : ℕ, ‖x ^ (m + 1) - y ^ (m + 1)‖ ≤ (m + 1) * ‖x - y‖ * r ^ m
  | 0 => by simp
  | (m + 1) => by
      have ih := norm_pow_succ_sub_pow_le hx hy m
      have hr : 0 ≤ r := (norm_nonneg _).trans hx
      have hid : x ^ (m + 1 + 1) - y ^ (m + 1 + 1) = x * (x ^ (m + 1) - y ^ (m + 1)) + (x - y) * y ^ (m + 1) := by
        ring
      rw [hid]
      calc ‖x * (x ^ (m + 1) - y ^ (m + 1)) + (x - y) * y ^ (m + 1)‖
          ≤ ‖x‖ * ‖x ^ (m + 1) - y ^ (m + 1)‖ + ‖x - y‖ * ‖y‖ ^ (m + 1) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_pow]
        _ ≤ r * ((m + 1) * ‖x - y‖ * r ^ m) + ‖x - y‖ * r ^ (m + 1) := by
            gcongr
        _ = ((m + 1 : ℕ) + 1 : ℝ) * ‖x - y‖ * r ^ (m + 1) := by push_cast; ring

/-- The polynomial `T` of (76), carried to order `ε⁴`. -/
noncomputable def Tpoly (e : ℝ) (b3 b4 b5 b6 : ℂ) : ℂ :=
  1 + (e:ℂ) * b3 + (e:ℂ) ^ 2 * (b4 + b3 ^ 2 / 2) + (e:ℂ) ^ 3 * (b5 + b3 * b4 + b3 ^ 3 / 6) +
    (e:ℂ) ^ 4 * (b6 + b3 * b5 + b4 ^ 2 / 2 + b3 ^ 2 * b4 / 2 + b3 ^ 4 / 24)

/-- `P = εb₃ + ε²b₄ + ε³b₅ + ε⁴b₆`. -/
def Ppoly (e : ℝ) (b3 b4 b5 b6 : ℂ) : ℂ :=
  (e:ℂ) * b3 + (e:ℂ) ^ 2 * b4 + (e:ℂ) ^ 3 * b5 + (e:ℂ) ^ 4 * b6

theorem norm_Ppoly_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {b3 b4 b5 b6 : ℂ} {β : ℝ}
    (h3 : ‖b3‖ ≤ β) (h4 : ‖b4‖ ≤ β) (h5 : ‖b5‖ ≤ β) (h6 : ‖b6‖ ≤ β) :
    ‖Ppoly e b3 b4 b5 b6‖ ≤ 4 * β := by
  unfold Ppoly
  have hE : ‖(e:ℂ)‖ = e := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
  have e2 : e ^ 2 ≤ 1 := pow_le_one₀ he0 he1
  have e3 : e ^ 3 ≤ 1 := pow_le_one₀ he0 he1
  have e4 : e ^ 4 ≤ 1 := pow_le_one₀ he0 he1
  have hβ : 0 ≤ β := (norm_nonneg _).trans h3
  calc ‖(e:ℂ) * b3 + (e:ℂ) ^ 2 * b4 + (e:ℂ) ^ 3 * b5 + (e:ℂ) ^ 4 * b6‖
      ≤ e * ‖b3‖ + e ^ 2 * ‖b4‖ + e ^ 3 * ‖b5‖ + e ^ 4 * ‖b6‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
        simp only [norm_mul, norm_pow, hE, le_refl]
    _ ≤ 1 * β + 1 * β + 1 * β + 1 * β := by gcongr
    _ = 4 * β := by ring

theorem expPoly_identity (E b3 b4 b5 b6 : ℂ) :
    ∑ m ∈ Finset.range 5, (E * b3 + E ^ 2 * b4 + E ^ 3 * b5 + E ^ 4 * b6) ^ m / (m ! : ℂ) -
      (1 + E * b3 + E ^ 2 * (b4 + b3 ^ 2 / 2) + E ^ 3 * (b5 + b3 * b4 + b3 ^ 3 / 6) +
        E ^ 4 * (b6 + b3 * b5 + b4 ^ 2 / 2 + b3 ^ 2 * b4 / 2 + b3 ^ 4 / 24)) =
      E ^ 2 / 2 * (((b3 + E * b4 + E ^ 2 * b5 + E ^ 3 * b6) ^ 2 - (b3 + E * b4 + E ^ 2 * b5) ^ 2) +
          (2 * E ^ 3 * b4 * b5 + E ^ 4 * b5 ^ 2)) +
      E ^ 3 / 6 * (((b3 + E * b4 + E ^ 2 * b5 + E ^ 3 * b6) ^ 3 - (b3 + E * b4) ^ 3) +
          (3 * E ^ 2 * b3 * b4 ^ 2 + E ^ 3 * b4 ^ 3)) +
      E ^ 4 / 24 * ((b3 + E * b4 + E ^ 2 * b5 + E ^ 3 * b6) ^ 4 - b3 ^ 4) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast; ring

set_option maxHeartbeats 2000000 in
theorem bound_core {E : ℂ} {e β : ℝ} (hE : ‖E‖ = e) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hβ : 0 ≤ β)
    {P1 Q1 Q2 b3 b4 b5 : ℂ} (h3 : ‖b3‖ ≤ β) (h4 : ‖b4‖ ≤ β) (h5 : ‖b5‖ ≤ β)
    (hP1 : ‖P1‖ ≤ 4 * β) (hQ1 : ‖Q1‖ ≤ 4 * β) (hQ2 : ‖Q2‖ ≤ 4 * β)
    (d4 : ‖P1 - b3‖ ≤ 3 * e * β) (d3 : ‖P1 - Q1‖ ≤ 2 * e ^ 2 * β) (d2 : ‖P1 - Q2‖ ≤ e ^ 3 * β) :
    ‖E ^ 2 / 2 * ((P1 ^ 2 - Q2 ^ 2) + (2 * E ^ 3 * b4 * b5 + E ^ 4 * b5 ^ 2)) +
      E ^ 3 / 6 * ((P1 ^ 3 - Q1 ^ 3) + (3 * E ^ 2 * b3 * b4 ^ 2 + E ^ 3 * b4 ^ 3)) +
      E ^ 4 / 24 * (P1 ^ 4 - b3 ^ 4)‖ ≤ 55 * e ^ 5 * (1 + β) ^ 4 := by
  have hb3 : ‖b3‖ ≤ 4 * β := by linarith
  have e32 : e ^ 3 ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 (by norm_num)
  have e43 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he0 he1 (by norm_num)
  have t4 : ‖P1 ^ 4 - b3 ^ 4‖ ≤ 768 * e * β ^ 4 := by
    have h := norm_pow_succ_sub_pow_le hP1 hb3 3
    have h' : ((3:ℕ) + 1 : ℝ) * ‖P1 - b3‖ * (4 * β) ^ 3 ≤ ((3:ℕ) + 1 : ℝ) * (3 * e * β) * (4 * β) ^ 3 := by
      gcongr
    calc ‖P1 ^ 4 - b3 ^ 4‖ ≤ ((3:ℕ) + 1 : ℝ) * (3 * e * β) * (4 * β) ^ 3 := h.trans h'
      _ = 768 * e * β ^ 4 := by push_cast; ring
  have t3a : ‖P1 ^ 3 - Q1 ^ 3‖ ≤ 96 * e ^ 2 * β ^ 3 := by
    have h := norm_pow_succ_sub_pow_le hP1 hQ1 2
    have h' : ((2:ℕ) + 1 : ℝ) * ‖P1 - Q1‖ * (4 * β) ^ 2 ≤ ((2:ℕ) + 1 : ℝ) * (2 * e ^ 2 * β) * (4 * β) ^ 2 := by
      gcongr
    calc ‖P1 ^ 3 - Q1 ^ 3‖ ≤ ((2:ℕ) + 1 : ℝ) * (2 * e ^ 2 * β) * (4 * β) ^ 2 := h.trans h'
      _ = 96 * e ^ 2 * β ^ 3 := by push_cast; ring
  have t2a : ‖P1 ^ 2 - Q2 ^ 2‖ ≤ 8 * e ^ 3 * β ^ 2 := by
    have h := norm_pow_succ_sub_pow_le hP1 hQ2 1
    have h' : ((1:ℕ) + 1 : ℝ) * ‖P1 - Q2‖ * (4 * β) ^ 1 ≤ ((1:ℕ) + 1 : ℝ) * (e ^ 3 * β) * (4 * β) ^ 1 := by
      gcongr
    calc ‖P1 ^ 2 - Q2 ^ 2‖ ≤ ((1:ℕ) + 1 : ℝ) * (e ^ 3 * β) * (4 * β) ^ 1 := h.trans h'
      _ = 8 * e ^ 3 * β ^ 2 := by push_cast; ring
  have t3b : ‖3 * E ^ 2 * b3 * b4 ^ 2 + E ^ 3 * b4 ^ 3‖ ≤ 4 * e ^ 2 * β ^ 3 := by
    have h1 : ‖3 * E ^ 2 * b3 * b4 ^ 2‖ ≤ 3 * e ^ 2 * β ^ 3 := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hE]
      have : ‖(3:ℂ)‖ = 3 := by norm_num
      rw [this]
      have := mul_le_mul h3 (pow_le_pow_left₀ (norm_nonneg _) h4 2) (by positivity) hβ
      nlinarith [pow_nonneg he0 2]
    have h2 : ‖E ^ 3 * b4 ^ 3‖ ≤ e ^ 2 * β ^ 3 := by
      rw [norm_mul, norm_pow, norm_pow, hE]
      have := pow_le_pow_left₀ (norm_nonneg _) h4 3
      have := mul_le_mul e32 this (by positivity) (by positivity)
      linarith
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 3 * e ^ 2 * β ^ 3 + e ^ 2 * β ^ 3 := add_le_add h1 h2
      _ = 4 * e ^ 2 * β ^ 3 := by ring
  have t2b : ‖2 * E ^ 3 * b4 * b5 + E ^ 4 * b5 ^ 2‖ ≤ 3 * e ^ 3 * β ^ 2 := by
    have h1 : ‖2 * E ^ 3 * b4 * b5‖ ≤ 2 * e ^ 3 * β ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, hE]
      have : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [this]
      have := mul_le_mul h4 h5 (norm_nonneg _) hβ
      nlinarith [pow_nonneg he0 3]
    have h2 : ‖E ^ 4 * b5 ^ 2‖ ≤ e ^ 3 * β ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, hE]
      have := pow_le_pow_left₀ (norm_nonneg _) h5 2
      have := mul_le_mul e43 this (by positivity) (by positivity)
      linarith
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 2 * e ^ 3 * β ^ 2 + e ^ 3 * β ^ 2 := add_le_add h1 h2
      _ = 3 * e ^ 3 * β ^ 2 := by ring
  have hT2 : ‖(P1 ^ 2 - Q2 ^ 2) + (2 * E ^ 3 * b4 * b5 + E ^ 4 * b5 ^ 2)‖ ≤ 11 * e ^ 3 * β ^ 2 := by
    refine (norm_add_le _ _).trans ?_; linarith
  have hT3 : ‖(P1 ^ 3 - Q1 ^ 3) + (3 * E ^ 2 * b3 * b4 ^ 2 + E ^ 3 * b4 ^ 3)‖ ≤ 100 * e ^ 2 * β ^ 3 := by
    refine (norm_add_le _ _).trans ?_; linarith
  have hn2 : ‖E ^ 2 / 2‖ = e ^ 2 / 2 := by rw [norm_div, norm_pow, hE]; norm_num
  have hn3 : ‖E ^ 3 / 6‖ = e ^ 3 / 6 := by rw [norm_div, norm_pow, hE]; norm_num
  have hn4 : ‖E ^ 4 / 24‖ = e ^ 4 / 24 := by rw [norm_div, norm_pow, hE]; norm_num
  have k2 : ‖E ^ 2 / 2 * ((P1 ^ 2 - Q2 ^ 2) + (2 * E ^ 3 * b4 * b5 + E ^ 4 * b5 ^ 2))‖ ≤
      e ^ 2 / 2 * (11 * e ^ 3 * β ^ 2) := by
    rw [norm_mul, hn2]; exact mul_le_mul_of_nonneg_left hT2 (by positivity)
  have k3 : ‖E ^ 3 / 6 * ((P1 ^ 3 - Q1 ^ 3) + (3 * E ^ 2 * b3 * b4 ^ 2 + E ^ 3 * b4 ^ 3))‖ ≤
      e ^ 3 / 6 * (100 * e ^ 2 * β ^ 3) := by
    rw [norm_mul, hn3]; exact mul_le_mul_of_nonneg_left hT3 (by positivity)
  have k4 : ‖E ^ 4 / 24 * (P1 ^ 4 - b3 ^ 4)‖ ≤ e ^ 4 / 24 * (768 * e * β ^ 4) := by
    rw [norm_mul, hn4]; exact mul_le_mul_of_nonneg_left t4 (by positivity)
  have h1β : (1:ℝ) ≤ 1 + β := by linarith
  have hb1 : β ^ 2 ≤ (1 + β) ^ 4 :=
    (pow_le_pow_left₀ hβ (by linarith) 2).trans (pow_le_pow_right₀ h1β (by norm_num))
  have hb2 : β ^ 3 ≤ (1 + β) ^ 4 :=
    (pow_le_pow_left₀ hβ (by linarith) 3).trans (pow_le_pow_right₀ h1β (by norm_num))
  have hb4 : β ^ 4 ≤ (1 + β) ^ 4 := pow_le_pow_left₀ hβ (by linarith) 4
  have h5 : 0 ≤ e ^ 5 := pow_nonneg he0 5
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add k2 k3) k4).trans ?_
  have hsum : e ^ 2 / 2 * (11 * e ^ 3 * β ^ 2) + e ^ 3 / 6 * (100 * e ^ 2 * β ^ 3) +
      e ^ 4 / 24 * (768 * e * β ^ 4) = e ^ 5 * (11 / 2 * β ^ 2 + 50 / 3 * β ^ 3 + 32 * β ^ 4) := by ring
  rw [hsum]
  calc e ^ 5 * (11 / 2 * β ^ 2 + 50 / 3 * β ^ 3 + 32 * β ^ 4)
      ≤ e ^ 5 * (11 / 2 * (1 + β) ^ 4 + 50 / 3 * (1 + β) ^ 4 + 32 * (1 + β) ^ 4) := by gcongr
    _ ≤ 55 * e ^ 5 * (1 + β) ^ 4 := by
        have : 0 ≤ e ^ 5 * (1 + β) ^ 4 := mul_nonneg h5 (pow_nonneg (by linarith) 4)
        nlinarith

/-- The fourth-order truncation of `e^P` differs from `T` by `O(ε⁵)`. -/
theorem expPoly_sub_T {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {b3 b4 b5 b6 : ℂ} {β : ℝ}
    (h3 : ‖b3‖ ≤ β) (h4 : ‖b4‖ ≤ β) (h5 : ‖b5‖ ≤ β) (h6 : ‖b6‖ ≤ β) :
    ‖∑ m ∈ Finset.range 5, Ppoly e b3 b4 b5 b6 ^ m / (m ! : ℂ) - Tpoly e b3 b4 b5 b6‖ ≤
      55 * e ^ 5 * (1 + β) ^ 4 := by
  have hE : ‖(e:ℂ)‖ = e := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
  have hβ : 0 ≤ β := (norm_nonneg _).trans h3
  unfold Ppoly Tpoly
  rw [expPoly_identity]
  have e2 : e ^ 2 ≤ 1 := pow_le_one₀ he0 he1
  have e3 : e ^ 3 ≤ 1 := pow_le_one₀ he0 he1
  have n1 : ∀ x : ℂ, ‖(e:ℂ) * x‖ = e * ‖x‖ := fun x => by rw [norm_mul, hE]
  have n2 : ∀ x : ℂ, ‖(e:ℂ) ^ 2 * x‖ = e ^ 2 * ‖x‖ := fun x => by rw [norm_mul, norm_pow, hE]
  have n3 : ∀ x : ℂ, ‖(e:ℂ) ^ 3 * x‖ = e ^ 3 * ‖x‖ := fun x => by rw [norm_mul, norm_pow, hE]
  apply bound_core hE he0 he1 hβ h3 h4 h5
  · calc _ ≤ ‖b3 + (e:ℂ) * b4 + (e:ℂ) ^ 2 * b5‖ + ‖(e:ℂ) ^ 3 * b6‖ := norm_add_le _ _
      _ ≤ (‖b3 + (e:ℂ) * b4‖ + ‖(e:ℂ) ^ 2 * b5‖) + ‖(e:ℂ) ^ 3 * b6‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖b3‖ + ‖(e:ℂ) * b4‖) + ‖(e:ℂ) ^ 2 * b5‖) + ‖(e:ℂ) ^ 3 * b6‖ := by gcongr; exact norm_add_le _ _
      _ = ‖b3‖ + e * ‖b4‖ + e ^ 2 * ‖b5‖ + e ^ 3 * ‖b6‖ := by rw [n1, n2, n3]
      _ ≤ β + 1 * β + 1 * β + 1 * β := by gcongr
      _ = 4 * β := by ring
  · calc _ ≤ ‖b3‖ + ‖(e:ℂ) * b4‖ := norm_add_le _ _
      _ = ‖b3‖ + e * ‖b4‖ := by rw [n1]
      _ ≤ β + 1 * β := by gcongr
      _ ≤ 4 * β := by linarith
  · calc _ ≤ ‖b3 + (e:ℂ) * b4‖ + ‖(e:ℂ) ^ 2 * b5‖ := norm_add_le _ _
      _ ≤ (‖b3‖ + ‖(e:ℂ) * b4‖) + ‖(e:ℂ) ^ 2 * b5‖ := by gcongr; exact norm_add_le _ _
      _ = ‖b3‖ + e * ‖b4‖ + e ^ 2 * ‖b5‖ := by rw [n1, n2]
      _ ≤ β + 1 * β + 1 * β := by gcongr
      _ ≤ 4 * β := by linarith
  · have : b3 + (e:ℂ) * b4 + (e:ℂ) ^ 2 * b5 + (e:ℂ) ^ 3 * b6 - b3 =
        (e:ℂ) * (b4 + (e:ℂ) * b5 + (e:ℂ) ^ 2 * b6) := by ring
    rw [this, n1]
    have : ‖b4 + (e:ℂ) * b5 + (e:ℂ) ^ 2 * b6‖ ≤ 3 * β := by
      calc _ ≤ ‖b4 + (e:ℂ) * b5‖ + ‖(e:ℂ) ^ 2 * b6‖ := norm_add_le _ _
        _ ≤ (‖b4‖ + ‖(e:ℂ) * b5‖) + ‖(e:ℂ) ^ 2 * b6‖ := by gcongr; exact norm_add_le _ _
        _ = ‖b4‖ + e * ‖b5‖ + e ^ 2 * ‖b6‖ := by rw [n1, n2]
        _ ≤ β + 1 * β + 1 * β := by gcongr
        _ = 3 * β := by ring
    calc e * ‖b4 + (e:ℂ) * b5 + (e:ℂ) ^ 2 * b6‖ ≤ e * (3 * β) := mul_le_mul_of_nonneg_left this he0
      _ = 3 * e * β := by ring
  · have : b3 + (e:ℂ) * b4 + (e:ℂ) ^ 2 * b5 + (e:ℂ) ^ 3 * b6 - (b3 + (e:ℂ) * b4) =
        (e:ℂ) ^ 2 * (b5 + (e:ℂ) * b6) := by ring
    rw [this, n2]
    have : ‖b5 + (e:ℂ) * b6‖ ≤ 2 * β := by
      calc _ ≤ ‖b5‖ + ‖(e:ℂ) * b6‖ := norm_add_le _ _
        _ = ‖b5‖ + e * ‖b6‖ := by rw [n1]
        _ ≤ β + 1 * β := by gcongr
        _ = 2 * β := by ring
    calc e ^ 2 * ‖b5 + (e:ℂ) * b6‖ ≤ e ^ 2 * (2 * β) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * e ^ 2 * β := by ring
  · have : b3 + (e:ℂ) * b4 + (e:ℂ) ^ 2 * b5 + (e:ℂ) ^ 3 * b6 - (b3 + (e:ℂ) * b4 + (e:ℂ) ^ 2 * b5) =
        (e:ℂ) ^ 3 * b6 := by ring
    rw [this, n3]
    exact mul_le_mul_of_nonneg_left h6 (by positivity)

/-- Abstract pointwise estimate: `|e^{P+Q} - T| ≤ X⁵eˣ + 4q(1+X)³ + 55ε⁵(1+β)⁴`. -/
theorem exp_sub_T_bound {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {b3 b4 b5 b6 : ℂ} {β : ℝ}
    (h3 : ‖b3‖ ≤ β) (h4 : ‖b4‖ ≤ β) (h5 : ‖b5‖ ≤ β) (h6 : ‖b6‖ ≤ β) {Q : ℂ} {q X : ℝ}
    (hQ : ‖Q‖ ≤ q) (hW : ‖Ppoly e b3 b4 b5 b6 + Q‖ ≤ X) (hP : ‖Ppoly e b3 b4 b5 b6‖ ≤ X) :
    ‖cexp (Ppoly e b3 b4 b5 b6 + Q) - Tpoly e b3 b4 b5 b6‖ ≤
      X ^ 5 * Real.exp X + 4 * q * (1 + X) ^ 3 + 55 * e ^ 5 * (1 + β) ^ 4 := by
  set P := Ppoly e b3 b4 b5 b6
  set W := P + Q
  have hX : 0 ≤ X := (norm_nonneg _).trans hP
  have hq : 0 ≤ q := (norm_nonneg _).trans hQ
  have i1 : ‖cexp W - ∑ m ∈ Finset.range 5, W ^ m / (m ! : ℂ)‖ ≤ X ^ 5 * Real.exp X := by
    refine (Complex.norm_exp_sub_sum_le_norm_mul_exp W 5).trans ?_
    gcongr
  have hd : ∀ m : ℕ, ‖W ^ (m + 1) - P ^ (m + 1)‖ ≤ (m + 1) * q * X ^ m := by
    intro m
    have := norm_pow_succ_sub_pow_le hW hP m
    have hWP : W - P = Q := by simp [W]
    rw [hWP] at this
    calc ‖W ^ (m + 1) - P ^ (m + 1)‖ ≤ (m + 1) * ‖Q‖ * X ^ m := this
      _ ≤ (m + 1) * q * X ^ m := by gcongr
  have i2 : ‖∑ m ∈ Finset.range 5, W ^ m / (m ! : ℂ) - ∑ m ∈ Finset.range 5, P ^ m / (m ! : ℂ)‖ ≤
      4 * q * (1 + X) ^ 3 := by
    have hsum : ∑ m ∈ Finset.range 5, W ^ m / (m ! : ℂ) - ∑ m ∈ Finset.range 5, P ^ m / (m ! : ℂ) =
        (W ^ (0 + 1) - P ^ (0 + 1)) + (W ^ (1 + 1) - P ^ (1 + 1)) / 2 +
          (W ^ (2 + 1) - P ^ (2 + 1)) / 6 + (W ^ (3 + 1) - P ^ (3 + 1)) / 24 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast; ring
    rw [hsum]
    have hn : ∀ (x : ℂ) (c : ℝ), 0 < c → ‖x / (c:ℂ)‖ = ‖x‖ / c := by
      intro x c hc; rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have e1 := hd 0
    have e2 := hd 1
    have e3 := hd 2
    have e4 := hd 3
    calc _ ≤ ‖W ^ (0 + 1) - P ^ (0 + 1)‖ + ‖(W ^ (1 + 1) - P ^ (1 + 1)) / 2‖ +
            ‖(W ^ (2 + 1) - P ^ (2 + 1)) / 6‖ + ‖(W ^ (3 + 1) - P ^ (3 + 1)) / 24‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ = ‖W ^ (0 + 1) - P ^ (0 + 1)‖ + ‖W ^ (1 + 1) - P ^ (1 + 1)‖ / 2 +
            ‖W ^ (2 + 1) - P ^ (2 + 1)‖ / 6 + ‖W ^ (3 + 1) - P ^ (3 + 1)‖ / 24 := by
          rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, show (6:ℂ) = ((6:ℝ):ℂ) by norm_num,
            show (24:ℂ) = ((24:ℝ):ℂ) by norm_num, hn _ 2 (by norm_num), hn _ 6 (by norm_num),
            hn _ 24 (by norm_num)]
      _ ≤ ((0:ℕ) + 1) * q * X ^ 0 + ((1:ℕ) + 1) * q * X ^ 1 / 2 + ((2:ℕ) + 1) * q * X ^ 2 / 6 +
            ((3:ℕ) + 1) * q * X ^ 3 / 24 := by
          gcongr
      _ ≤ 4 * q * (1 + X) ^ 3 := by
          push_cast
          have h1 : (1:ℝ) ≤ (1 + X) ^ 3 := one_le_pow₀ (by linarith)
          have h2 : X ≤ (1 + X) ^ 3 := by nlinarith [sq_nonneg X]
          have h3 : X ^ 2 ≤ (1 + X) ^ 3 := by nlinarith [sq_nonneg X, mul_nonneg hX (sq_nonneg X)]
          have h4 : X ^ 3 ≤ (1 + X) ^ 3 := pow_le_pow_left₀ hX (by linarith) 3
          have : 0 ≤ q * (1 + X) ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hq,
            mul_le_mul_of_nonneg_left h3 hq, mul_le_mul_of_nonneg_left h4 hq]
  have i3 := expPoly_sub_T he0 he1 h3 h4 h5 h6
  calc ‖cexp W - Tpoly e b3 b4 b5 b6‖
      = ‖(cexp W - ∑ m ∈ Finset.range 5, W ^ m / (m ! : ℂ)) +
          (∑ m ∈ Finset.range 5, W ^ m / (m ! : ℂ) - ∑ m ∈ Finset.range 5, P ^ m / (m ! : ℂ)) +
          (∑ m ∈ Finset.range 5, P ^ m / (m ! : ℂ) - Tpoly e b3 b4 b5 b6)‖ := by congr 1; ring
    _ ≤ X ^ 5 * Real.exp X + 4 * q * (1 + X) ^ 3 + 55 * e ^ 5 * (1 + β) ^ 4 :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add i1 i2)) i3)

end EulerianBridge.Saddle
