/-
Uniform Lanczos note, Corollary: the expansion of the limit profile at `α = 0`, now with the
expansion of `I'` proved (no hypothesis left).

* `exp9`        : `|eˣ - Σ_{k≤8} xᵏ/k!| ≤ |x|⁹/326592` for `|x| ≤ 1` (Mathlib's `Real.exp_bound`);
* `E_bound`     : `|u cosh u - sinh u - (u²/3) sinh u + (u⁴/45) sinh u| ≤ u⁷/400` on `[0,1]`;
* `Lp_taylor`   : `|Λ'(s) - (s/12 - s³/720)| ≤ s⁵/25600` for `0 < s ≤ 2`;
* `Ip_expansion`: `|I'(x) - 12x - (144/5)x³| ≤ 520 x⁵` for `0 ≤ x ≤ Λ'(1)`;
* `F_expansion` : there are `b > 0` and `K` such that for `0 ≤ a ≤ b`, with `α = H(a)`,
  `|a²/4 - (α/12 - α²/20)| ≤ K α³`, i.e. `F(α) = α/12 - α²/20 + O(α³)`.
-/
import UniformLanczos.Lambda
import UniformLanczos.EndpointConcrete
import UniformLanczos.Corollary

open Set Real

namespace UniformLanczos

lemma exp9 {x : ℝ} (hx : |x| ≤ 1) :
    |exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720
      + x ^ 7 / 5040 + x ^ 8 / 40320)| ≤ |x| ^ 9 / 326592 := by
  have h := Real.exp_bound hx (n := 9) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  convert h using 2
  try ring

lemma sinh_cosh_approx {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |sinh u - (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)| ≤ u ^ 9 / 326592 ∧
    |cosh u - (1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720 + u ^ 8 / 40320)| ≤ u ^ 9 / 326592 := by
  have hp := exp9 (x := u) (by rw [abs_of_nonneg h0]; exact h1)
  have hm := exp9 (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hp
  rw [abs_neg, abs_of_nonneg h0] at hm
  rw [abs_le] at hp hm
  constructor
  · rw [sinh_eq, abs_le]; constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  · rw [cosh_eq, abs_le]; constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]

lemma E_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |u * cosh u - sinh u - u ^ 2 / 3 * sinh u + u ^ 4 / 45 * sinh u| ≤ u ^ 7 / 400 := by
  obtain ⟨hs, hc⟩ := sinh_cosh_approx h0 h1
  set ds := sinh u - (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040) with hds
  set dc := cosh u - (1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720 + u ^ 8 / 40320) with hdc
  have hid : u * cosh u - sinh u - u ^ 2 / 3 * sinh u + u ^ 4 / 45 * sinh u =
      (2 / 945 * u ^ 7 + 29 / 201600 * u ^ 9 + 1 / 226800 * u ^ 11)
        + u * dc - (1 + u ^ 2 / 3 - u ^ 4 / 45) * ds := by
    rw [hds, hdc]; ring
  rw [hid]
  have hu7 : 0 ≤ u ^ 7 := pow_nonneg h0 7
  have h97 : u ^ 9 ≤ u ^ 7 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h117 : u ^ 11 ≤ u ^ 7 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have hu4 : u ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have hcoef : 0 ≤ 1 + u ^ 2 / 3 - u ^ 4 / 45 := by nlinarith [sq_nonneg u, pow_nonneg h0 4]
  have hcoef2 : 1 + u ^ 2 / 3 - u ^ 4 / 45 ≤ 2 := by nlinarith [pow_nonneg h0 4]
  have hP0 : 0 ≤ 2 / 945 * u ^ 7 + 29 / 201600 * u ^ 9 + 1 / 226800 * u ^ 11 := by positivity
  have hP1 : 2 / 945 * u ^ 7 + 29 / 201600 * u ^ 9 + 1 / 226800 * u ^ 11 ≤
      (2 / 945 + 29 / 201600 + 1 / 226800) * u ^ 7 := by nlinarith
  have hdc' : |u * dc| ≤ u ^ 7 / 326592 := by
    rw [abs_mul, abs_of_nonneg h0]
    calc u * |dc| ≤ 1 * (u ^ 9 / 326592) := mul_le_mul h1 hc (abs_nonneg _) (by norm_num)
      _ ≤ u ^ 7 / 326592 := by linarith
  have hds' : |(1 + u ^ 2 / 3 - u ^ 4 / 45) * ds| ≤ 2 * (u ^ 7 / 326592) := by
    rw [abs_mul, abs_of_nonneg hcoef]
    calc (1 + u ^ 2 / 3 - u ^ 4 / 45) * |ds| ≤ 2 * (u ^ 9 / 326592) :=
          mul_le_mul hcoef2 hs (abs_nonneg _) (by norm_num)
      _ ≤ 2 * (u ^ 7 / 326592) := by linarith
  rw [abs_le] at hdc' hds' ⊢
  constructor <;> nlinarith [hdc'.1, hdc'.2, hds'.1, hds'.2]

theorem Lp_taylor {s : ℝ} (h0 : 0 < s) (h2 : s ≤ 2) :
    |Lp s - (s / 12 - s ^ 3 / 720)| ≤ s ^ 5 / 25600 := by
  set u := s / 2 with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  have hsu : s = 2 * u := by rw [hu]; ring
  have hsh : 0 < sinh u := sinh_pos_iff.mpr hu0
  have hsl : u < sinh u := self_lt_sinh_iff.mpr hu0
  have hE := E_bound hu0.le hu1
  have hD : 0 < 2 * u * sinh u := by positivity
  have hrepr : Lp s - (s / 12 - s ^ 3 / 720) =
      (u * cosh u - sinh u - u ^ 2 / 3 * sinh u + u ^ 4 / 45 * sinh u) / (2 * u * sinh u) := by
    rw [Lp_hyp h0.ne', ← hu, hsu]
    field_simp
    ring
  rw [hrepr, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hD2 : 2 * u ^ 2 ≤ 2 * u * sinh u := by nlinarith
  calc |u * cosh u - sinh u - u ^ 2 / 3 * sinh u + u ^ 4 / 45 * sinh u| ≤ u ^ 7 / 400 := hE
    _ = s ^ 5 / 25600 * (2 * u ^ 2) := by rw [hsu]; ring
    _ ≤ s ^ 5 / 25600 * (2 * u * sinh u) := by
        apply mul_le_mul_of_nonneg_left hD2; positivity

theorem Ip_expansion {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Lp 1) :
    |Ip x - (12 * x + 144 / 5 * x ^ 3)| ≤ 520 * x ^ 5 := by
  have hL1 : Lp 1 < 1 / 2 := Lp_lt_half one_pos
  have hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
  have h1m : Lp 1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [Lp_pos one_pos], hL1⟩
  set σ := Ip x with hσdef
  have hσ0 : 0 ≤ σ := Ip_nonneg h0 (by linarith)
  have hσ1 : σ ≤ 1 := by
    have := Ip_strictMonoOn.monotoneOn hx h1m h1
    rwa [Ip_Lp] at this
  have hxσ : Lp σ = x := Lp_Ip hx
  rcases eq_or_lt_of_le hσ0 with hz | hσpos
  · have : x = 0 := by rw [← hxσ, ← hz, Lp_zero]
    rw [this, ← hz]; norm_num
  have hT := Lp_taylor hσpos (by linarith)
  rw [hxσ] at hT
  set r := x - (σ / 12 - σ ^ 3 / 720) with hr
  have hr' := abs_le.mp hT
  have hσ5 : σ ^ 5 ≤ σ := by
    calc σ ^ 5 ≤ σ ^ 1 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
      _ = σ := pow_one σ
  have hσ3 : σ ^ 3 ≤ σ := by
    calc σ ^ 3 ≤ σ ^ 1 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
      _ = σ := pow_one σ
  -- σ ≤ 13 x
  have hσx : σ ≤ 13 * x := by nlinarith [hr'.1]
  -- d = σ - 12x = σ³/60 - 12 r
  have hd : σ - 12 * x = σ ^ 3 / 60 - 12 * r := by rw [hr]; ring
  have hσ35 : σ ^ 5 ≤ σ ^ 3 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
  have hdabs : |σ - 12 * x| ≤ σ ^ 3 / 50 := by
    rw [hd, abs_le]; constructor <;> nlinarith [hr'.1, hr'.2, pow_nonneg hσ0 3]
  have hcube : σ ^ 3 ≤ (13 * x) ^ 3 := pow_le_pow_left₀ hσ0 hσx 3
  have hquad : σ ^ 2 + 12 * x * σ + 144 * x ^ 2 ≤ 469 * x ^ 2 := by
    have h2 : σ ^ 2 ≤ (13 * x) ^ 2 := pow_le_pow_left₀ hσ0 hσx 2
    nlinarith [mul_le_mul_of_nonneg_left hσx (by linarith : (0:ℝ) ≤ 12 * x)]
  have hquad0 : 0 ≤ σ ^ 2 + 12 * x * σ + 144 * x ^ 2 := by positivity
  have hdiff : σ ^ 3 - 1728 * x ^ 3 = (σ - 12 * x) * (σ ^ 2 + 12 * x * σ + 144 * x ^ 2) := by ring
  have hdiffabs : |σ ^ 3 - 1728 * x ^ 3| ≤ (13 * x) ^ 3 / 50 * (469 * x ^ 2) := by
    rw [hdiff, abs_mul, abs_of_nonneg hquad0]
    apply mul_le_mul _ hquad hquad0 (by positivity)
    linarith
  have hrabs : |12 * r| ≤ 12 * (13 * x) ^ 5 / 25600 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 12)]
    have h5 : σ ^ 5 ≤ (13 * x) ^ 5 := pow_le_pow_left₀ hσ0 hσx 5
    have : |r| ≤ σ ^ 5 / 25600 := hT
    nlinarith
  have htarget : σ - (12 * x + 144 / 5 * x ^ 3) = (σ ^ 3 - 1728 * x ^ 3) / 60 - 12 * r := by
    rw [hr]; ring
  rw [htarget]
  have hx5 : 0 ≤ x ^ 5 := pow_nonneg h0 5
  calc |(σ ^ 3 - 1728 * x ^ 3) / 60 - 12 * r|
      ≤ |(σ ^ 3 - 1728 * x ^ 3) / 60| + |12 * r| := abs_sub _ _
    _ ≤ (13 * x) ^ 3 / 50 * (469 * x ^ 2) / 60 + 12 * (13 * x) ^ 5 / 25600 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 60)]
        gcongr
    _ ≤ 520 * x ^ 5 := by nlinarith

theorem F_expansion : ∃ b > 0, ∃ K : ℝ, ∀ a ∈ Icc 0 b,
    |a ^ 2 / 4 - (Hint (fun y => y * Ip y) a / 12 - Hint (fun y => y * Ip y) a ^ 2 / 20)|
      ≤ K * Hint (fun y => y * Ip y) a ^ 3 := by
  set b := min (Lp 1) (1 / 5) with hb
  have hL1 : 0 < Lp 1 := Lp_pos one_pos
  have hL2 : Lp 1 < 1 / 2 := Lp_lt_half one_pos
  have hbpos : 0 < b := lt_min hL1 (by norm_num)
  have hbL : b ≤ Lp 1 := min_le_left _ _
  have hb5 : b ≤ 1 / 5 := min_le_right _ _
  set K0 : ℝ := 260 / 12 + (162 / 5 + 729 / 25 + 6 * 260 + 54 / 5 * 260 + 260 ^ 2) / 20
  refine ⟨b, hbpos, K0 / 8, ?_⟩
  intro a ha
  have hIc : ContinuousOn Ip (Icc 0 b) :=
    Ip_continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hexp : ∀ x ∈ Icc 0 b, |Ip x - (12 * x + 144 / 5 * x ^ 3)| ≤ 520 * x ^ 5 :=
    fun x hx => Ip_expansion hx.1 (le_trans hx.2 hbL)
  have hH := Hint_expansion (b := b) (C := 520) (by norm_num) hIc hexp a ha
  set α := Hint (fun y => y * Ip y) a with hα
  set A := a ^ 2 with hA
  have hA0 : 0 ≤ A := sq_nonneg a
  have ha5 : a ≤ 1 / 5 := le_trans ha.2 hb5
  have hA1 : A ≤ 1 / 25 := by rw [hA]; nlinarith [ha.1]
  set r := α - (3 * A + 27 / 5 * A ^ 2) with hr
  have hαr : α = 3 * A + 27 / 5 * A ^ 2 + r := by rw [hr]; ring
  have hrA : |r| ≤ 260 * A ^ 3 := by
    have : |α - (3 * a ^ 2 + 27 / 5 * a ^ 4)| ≤ 520 * a ^ 6 / 2 := hH
    have e1 : 3 * a ^ 2 + 27 / 5 * a ^ 4 = 3 * A + 27 / 5 * A ^ 2 := by rw [hA]; ring
    have e2 : 520 * a ^ 6 / 2 = 260 * A ^ 3 := by rw [hA]; ring
    rw [e1, e2] at this; exact this
  have hinv := inversion hA0 (by linarith) (by norm_num : (0:ℝ) ≤ 260) hαr hrA
  have hsmall : 260 * A ^ 2 ≤ 1 := by nlinarith
  have hA2 := A_le_half_alpha hA0 hαr hrA hsmall
  have hA3 : A ^ 3 ≤ α ^ 3 / 8 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 2 * A) hA2 3
    nlinarith
  have hK0 : 0 ≤ K0 := by positivity
  calc |A / 4 - (α / 12 - α ^ 2 / 20)| ≤ K0 * A ^ 3 := hinv
    _ ≤ K0 * (α ^ 3 / 8) := mul_le_mul_of_nonneg_left hA3 hK0
    _ = K0 / 8 * α ^ 3 := by ring

end UniformLanczos
