import Mathlib

/-! # Manuscript 12, Theorem 5.14: weighted strong monotonicity

This module formalises the second half of the proof of Theorem 5.14 (Subsection 5.8),
from the paragraph "Weighted strong monotonicity" to (ul-rate-energy).

Data: a window `W ⊂ ℤ`, the symmetric positive semidefinite matrix `B̄` on `W`
with a summable second moment of its rows, the diagonal coefficients `μ_k ≥ μ₀ > 0`,
the difference `d = a - b̃` and the residual difference `h = B̄ d + μ d`.
With the weights `ω_k = (1 + ε|k-j|)^{-2}`:

* `weighted_coercivity`: `(μ₀/2) Σ ω d² ≤ Σ ω d h` when `ε² S ≤ μ₀` (ul-rate-coercivity);
* `weighted_energy_bound`: `Σ ω d² ≤ (4/μ₀²) Σ ω h²`, hence `d_j² ≤ (4/μ₀²) Σ ω h²`
  (ul-rate-energy);
* `residual_weighted_sum`: on `W = [j-L, j+L]`, the hybrid bound
  `|h_k| ≤ C (1/M + (1+D_k)^{-4})` (ul-rate-resid-hybrid) gives
  `Σ ω h² ≤ C' (1/M² + 1/L²)`;
* `row_moment_bound`: the decay `|B̄_{km}| ≤ C (1+|k-m|)^{-5}` gives uniformly bounded
  row sums of `(k-m)² |B̄_{km}|`.

Nothing here is a classical result: it is the original argument of the manuscript. -/

namespace UniformLanczos.Rate514

open Finset

/-! ## Weights -/

/-- `s_k = (1 + ε|k-j|)⁻¹`, so that the weight of the manuscript is `ω_k = s_k²`. -/
noncomputable def sw (ε : ℝ) (j k : ℤ) : ℝ := (1 + ε * |(k:ℝ) - j|)⁻¹

/-- The weight `ω_k = (1 + ε|k-j|)^{-2}`. -/
noncomputable def ω (ε : ℝ) (j k : ℤ) : ℝ := sw ε j k ^ 2

theorem one_add_pos {ε : ℝ} (hε : 0 ≤ ε) (j k : ℤ) : 0 < 1 + ε * |(k:ℝ) - j| := by
  have := mul_nonneg hε (abs_nonneg ((k:ℝ) - j)); linarith

theorem sw_pos {ε : ℝ} (hε : 0 ≤ ε) (j k : ℤ) : 0 < sw ε j k :=
  inv_pos.mpr (one_add_pos hε j k)

theorem sw_le_one {ε : ℝ} (hε : 0 ≤ ε) (j k : ℤ) : sw ε j k ≤ 1 := by
  unfold sw
  apply inv_le_one_of_one_le₀
  have := mul_nonneg hε (abs_nonneg ((k:ℝ) - j)); linarith

theorem ω_nonneg (ε : ℝ) (j k : ℤ) : 0 ≤ ω ε j k := sq_nonneg _

theorem ω_self (ε : ℝ) (j : ℤ) : ω ε j j = 1 := by simp [ω, sw]

/-- `(s_k - s_m)² ≤ ε² (k-m)² s_k s_m`. -/
theorem sw_sub_sq_le {ε : ℝ} (hε : 0 ≤ ε) (j k m : ℤ) :
    (sw ε j k - sw ε j m) ^ 2 ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * (sw ε j k * sw ε j m) := by
  set xk := 1 + ε * |(k:ℝ) - j|
  set xm := 1 + ε * |(m:ℝ) - j|
  have hxk : 1 ≤ xk := by have := mul_nonneg hε (abs_nonneg ((k:ℝ) - j)); linarith
  have hxm : 1 ≤ xm := by have := mul_nonneg hε (abs_nonneg ((m:ℝ) - j)); linarith
  have hdiff : (xm - xk) ^ 2 ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 := by
    have h1 : |(|(m:ℝ) - j| - |(k:ℝ) - j|)| ≤ |((m:ℝ) - j) - ((k:ℝ) - j)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    have h2 : ((m:ℝ) - j) - ((k:ℝ) - j) = -((k:ℝ) - m) := by ring
    rw [h2, abs_neg] at h1
    have h3 : (|(m:ℝ) - j| - |(k:ℝ) - j|) ^ 2 ≤ ((k:ℝ) - m) ^ 2 := by
      rw [← sq_abs, ← sq_abs ((k:ℝ) - m)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h4 : xm - xk = ε * (|(m:ℝ) - j| - |(k:ℝ) - j|) := by simp only [xm, xk]; ring
    rw [h4, mul_pow]
    exact mul_le_mul_of_nonneg_left h3 (sq_nonneg ε)
  have hk0 : xk ≠ 0 := by linarith
  have hm0 : xm ≠ 0 := by linarith
  have hsub : sw ε j k - sw ε j m = (xm - xk) * (sw ε j k * sw ε j m) := by
    simp only [sw, xk, xm] at *
    field_simp
  have hprod : 0 ≤ sw ε j k * sw ε j m := (mul_pos (sw_pos hε j k) (sw_pos hε j m)).le
  have hxx : sw ε j k * sw ε j m * (xk * xm) = 1 := by
    simp only [sw, xk, xm]; field_simp
  rw [hsub, mul_pow]
  calc (xm - xk) ^ 2 * (sw ε j k * sw ε j m) ^ 2
      ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * (xk * xm) * (sw ε j k * sw ε j m) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have : 1 ≤ xk * xm := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ((k:ℝ) - m))]
    _ = ε ^ 2 * ((k:ℝ) - m) ^ 2 * (sw ε j k * sw ε j m) *
          (sw ε j k * sw ε j m * (xk * xm)) := by ring
    _ = ε ^ 2 * ((k:ℝ) - m) ^ 2 * (sw ε j k * sw ε j m) := by rw [hxx, mul_one]

/-! ## The weighted quadratic form -/

/-- Symmetrisation: `Σ s_k² d_k (B d)_k = ⟨s d, B s d⟩ + ½ Σ (s_k - s_m)² B_{km} d_k d_m`. -/
theorem quad_split (W : Finset ℤ) (B : ℤ → ℤ → ℝ) (s d : ℤ → ℝ)
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k) :
    ∑ k ∈ W, s k ^ 2 * d k * ∑ m ∈ W, B k m * d m =
      ∑ k ∈ W, ∑ m ∈ W, B k m * (s k * d k) * (s m * d m) +
        (1/2) * ∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m := by
  have hT2 : ∑ k ∈ W, ∑ m ∈ W, s m ^ 2 * B k m * d k * d m =
      ∑ k ∈ W, ∑ m ∈ W, s k ^ 2 * B k m * d k * d m := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun m hm => ?_
    rw [hsym m hm k hk]; ring
  have hL : ∑ k ∈ W, s k ^ 2 * d k * ∑ m ∈ W, B k m * d m =
      ∑ k ∈ W, ∑ m ∈ W, s k ^ 2 * B k m * d k * d m := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hR : ∑ k ∈ W, ∑ m ∈ W, B k m * (s k * d k) * (s m * d m) +
        (1/2) * ∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m =
      (1/2) * ∑ k ∈ W, ∑ m ∈ W, s k ^ 2 * B k m * d k * d m +
        (1/2) * ∑ k ∈ W, ∑ m ∈ W, s m ^ 2 * B k m * d k * d m := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hL, hR, hT2]
  ring

/-- The correction term of the symmetrisation is at least `-(ε² S/2) Σ s² d²`. -/
theorem correction_lower (W : Finset ℤ) (B : ℤ → ℤ → ℝ) (s d : ℤ → ℝ) (ε S : ℝ)
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hss : ∀ k m : ℤ, (s k - s m) ^ 2 ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * (s k * s m))
    (hrow : ∀ k ∈ W, ∑ m ∈ W, ((k:ℝ) - m) ^ 2 * |B k m| ≤ S) :
    -(ε ^ 2 * S / 2) * ∑ k ∈ W, s k ^ 2 * d k ^ 2 ≤
      (1/2) * ∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m := by
  set P : ℤ → ℤ → ℝ := fun k m => ((k:ℝ) - m) ^ 2 * |B k m|
  have hterm : ∀ k m : ℤ, |(s k - s m) ^ 2 * B k m * d k * d m| ≤
      ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) := by
    intro k m
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 := hss k m
    have h2 : s k * s m * (|d k| * |d m|) ≤ (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) / 2 := by
      nlinarith [sq_nonneg (s k * |d k| - s m * |d m|), sq_abs (d k), sq_abs (d m)]
    have hB := abs_nonneg (B k m)
    have hdd : 0 ≤ |d k| * |d m| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hE : 0 ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * |B k m| :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hB
    calc (s k - s m) ^ 2 * |B k m| * |d k| * |d m|
        = (s k - s m) ^ 2 * (|B k m| * (|d k| * |d m|)) := by ring
      _ ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * (s k * s m) * (|B k m| * (|d k| * |d m|)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hB hdd)
      _ = ε ^ 2 * ((k:ℝ) - m) ^ 2 * |B k m| * (s k * s m * (|d k| * |d m|)) := by ring
      _ ≤ ε ^ 2 * ((k:ℝ) - m) ^ 2 * |B k m| *
            ((s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h2 hE
      _ = ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) := by
          simp only [P]; ring
  have hPsym : ∀ k ∈ W, ∀ m ∈ W, P k m = P m k := by
    intro k hk m hm; simp only [P]; rw [hsym k hk m hm]; ring
  have hswap : ∑ k ∈ W, ∑ m ∈ W, P k m * (s m ^ 2 * d m ^ 2) =
      ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun m hm => ?_
    rw [hPsym m hm k hk]
  have hrow' : ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) ≤
      S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow k hk) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have habs : |∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m| ≤
      ε ^ 2 * S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by
    calc |∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m|
        ≤ ∑ k ∈ W, |∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ W, ∑ m ∈ W, |(s k - s m) ^ 2 * B k m * d k * d m| :=
          Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ W, ∑ m ∈ W, ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun m _ => hterm k m
      _ = ε ^ 2 / 2 * (∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) +
            ∑ k ∈ W, ∑ m ∈ W, P k m * (s m ^ 2 * d m ^ 2)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = ε ^ 2 * ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) := by rw [hswap]; ring
      _ ≤ ε ^ 2 * (S * ∑ k ∈ W, s k ^ 2 * d k ^ 2) :=
          mul_le_mul_of_nonneg_left hrow' (sq_nonneg ε)
      _ = ε ^ 2 * S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by ring
  have := neg_abs_le (∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m)
  linarith

/-- **Weighted coercivity, (ul-rate-coercivity).** If `B̄` is symmetric and positive
semidefinite on `W`, the second moments of its rows are at most `S`, `μ_k ≥ μ₀`,
`h = B̄ d + μ d` on `W`, and `ε² S ≤ μ₀`, then `(μ₀/2) Σ ω d² ≤ Σ ω d h`. -/
theorem weighted_coercivity (W : Finset ℤ) (j : ℤ) {ε : ℝ} (hε : 0 ≤ ε)
    (B : ℤ → ℤ → ℝ) (d h μ : ℤ → ℝ) {μ₀ S : ℝ}
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, B k m * x k * x m)
    (hrow : ∀ k ∈ W, ∑ m ∈ W, ((k:ℝ) - m) ^ 2 * |B k m| ≤ S)
    (hμ : ∀ k ∈ W, μ₀ ≤ μ k)
    (hh : ∀ k ∈ W, h k = ∑ m ∈ W, B k m * d m + μ k * d k)
    (hsmall : ε ^ 2 * S ≤ μ₀) :
    μ₀ / 2 * ∑ k ∈ W, ω ε j k * d k ^ 2 ≤ ∑ k ∈ W, ω ε j k * d k * h k := by
  have hsplit := quad_split W B (sw ε j) d hsym
  have hcorr := correction_lower W B (sw ε j) d ε S hsym
    (fun k m => sw_sub_sq_le hε j k m) hrow
  have hpos := hpsd (fun k => sw ε j k * d k)
  have hexp : ∑ k ∈ W, ω ε j k * d k * h k =
      ∑ k ∈ W, sw ε j k ^ 2 * d k * ∑ m ∈ W, B k m * d m +
        ∑ k ∈ W, μ k * (ω ε j k * d k ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hh k hk, ω]; ring
  have hdiag : μ₀ * ∑ k ∈ W, ω ε j k * d k ^ 2 ≤ ∑ k ∈ W, μ k * (ω ε j k * d k ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hμ k hk) (mul_nonneg (ω_nonneg ε j k) (sq_nonneg _))
  have hω : ∑ k ∈ W, sw ε j k ^ 2 * d k ^ 2 = ∑ k ∈ W, ω ε j k * d k ^ 2 := rfl
  have hX : 0 ≤ ∑ k ∈ W, ω ε j k * d k ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (ω_nonneg ε j k) (sq_nonneg _)
  rw [hω] at hcorr
  rw [hexp, hsplit]
  nlinarith

/-- **Energy bound, (ul-rate-energy).** Coercivity with constant `μ₀/2` gives
`Σ ω d² ≤ (4/μ₀²) Σ ω h²`. -/
theorem energy_of_coercive (W : Finset ℤ) (w d h : ℤ → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hw : ∀ k ∈ W, 0 ≤ w k)
    (hc : μ / 2 * ∑ k ∈ W, w k * d k ^ 2 ≤ ∑ k ∈ W, w k * d k * h k) :
    ∑ k ∈ W, w k * d k ^ 2 ≤ 4 / μ ^ 2 * ∑ k ∈ W, w k * h k ^ 2 := by
  set X := ∑ k ∈ W, w k * d k ^ 2
  set P := ∑ k ∈ W, w k * d k * h k
  set Y := ∑ k ∈ W, w k * h k ^ 2
  have hs : 0 ≤ ∑ k ∈ W, w k * (μ / 2 * d k - h k) ^ 2 :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (sq_nonneg _)
  have he : ∑ k ∈ W, w k * (μ / 2 * d k - h k) ^ 2 = (μ / 2) ^ 2 * X - 2 * (μ / 2) * P + Y := by
    simp only [X, P, Y, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [he] at hs
  have hμ2 : 0 < μ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ2]
  nlinarith

/-- The value at the centre: `d_j² ≤ Σ ω d²`, since `ω_j = 1`. -/
theorem centre_le (W : Finset ℤ) (j : ℤ) (hj : j ∈ W) (ε : ℝ) (d : ℤ → ℝ) :
    d j ^ 2 ≤ ∑ k ∈ W, ω ε j k * d k ^ 2 := by
  have h := Finset.single_le_sum (f := fun k => ω ε j k * d k ^ 2)
    (fun k _ => mul_nonneg (ω_nonneg ε j k) (sq_nonneg _)) hj
  simpa [ω_self] using h

/-- **Pointwise bound at the centre.** Under the hypotheses of `weighted_coercivity`,
`d_j² ≤ (4/μ₀²) Σ_{k ∈ W} ω_k h_k²`. -/
theorem centre_bound (W : Finset ℤ) (j : ℤ) (hj : j ∈ W) {ε : ℝ} (hε : 0 ≤ ε)
    (B : ℤ → ℤ → ℝ) (d h μ : ℤ → ℝ) {μ₀ S : ℝ} (hμ₀ : 0 < μ₀)
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, B k m * x k * x m)
    (hrow : ∀ k ∈ W, ∑ m ∈ W, ((k:ℝ) - m) ^ 2 * |B k m| ≤ S)
    (hμ : ∀ k ∈ W, μ₀ ≤ μ k)
    (hh : ∀ k ∈ W, h k = ∑ m ∈ W, B k m * d m + μ k * d k)
    (hsmall : ε ^ 2 * S ≤ μ₀) :
    d j ^ 2 ≤ 4 / μ₀ ^ 2 * ∑ k ∈ W, ω ε j k * h k ^ 2 :=
  (centre_le W j hj ε d).trans <| energy_of_coercive W (ω ε j) d h hμ₀
    (fun k _ => ω_nonneg ε j k)
    (weighted_coercivity W j hε B d h μ hsym hpsd hrow hμ hh hsmall)

/-! ## Summable profiles on `ℤ` -/

/-- `n ↦ (1 + ε|n|)^{-p}` is summable on `ℤ` for `ε > 0` and `p ≥ 2`. -/
theorem summable_profile {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun n : ℤ => ((1 + ε * |(n:ℝ)|) ^ p)⁻¹) := by
  have hb : (1:ℝ) < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow hb).mul_left ((ε ^ p)⁻¹)) ?_
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0:ℤ))] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 from hn)
  have ha : 0 < |(n:ℝ)| := abs_pos.mpr hn0
  have hpos : 0 < 1 + ε * |(n:ℝ)| := by positivity
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hpos.le _)), Real.rpow_neg ha.le,
    Real.rpow_natCast, ← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- A finite sum along an injective reindexing is at most the full series. -/
theorem sum_le_tsum_of_injOn {A : Finset ℤ} (φ : ℤ → ℤ) {g : ℤ → ℝ}
    (hinj : ∀ x ∈ A, ∀ y ∈ A, φ x = φ y → x = y) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    ∑ k ∈ A, g (φ k) ≤ ∑' n, g n := by
  rw [← Finset.sum_image hinj]
  exact hg.sum_le_tsum _ (fun n _ => hg0 n)

/-! ## The decay kernel has uniformly bounded second row moments -/

/-- `Z₃ = Σ_{n ∈ ℤ} (1+|n|)^{-3}`. -/
noncomputable def Z3 : ℝ := ∑' n : ℤ, ((1 + 1 * |(n:ℝ)|) ^ 3)⁻¹

/-- **Row moments.** If `|B̄_{km}| ≤ C (1+|k-m|)^{-5}`, then for every finite window and
every row, `Σ_m (k-m)² |B̄_{km}| ≤ C Z₃`. -/
theorem row_moment_bound (W : Finset ℤ) (B : ℤ → ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ k m : ℤ, |B k m| ≤ C * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) (k : ℤ) :
    ∑ m ∈ W, ((k:ℝ) - m) ^ 2 * |B k m| ≤ C * Z3 := by
  have hterm : ∀ m : ℤ, ((k:ℝ) - m) ^ 2 * |B k m| ≤
      C * ((1 + 1 * |((k - m : ℤ) : ℝ)|) ^ 3)⁻¹ := by
    intro m
    have hcast : ((k - m : ℤ) : ℝ) = (k:ℝ) - m := by push_cast; ring
    rw [hcast, one_mul]
    set a := |(k:ℝ) - m|
    have ha : 0 ≤ a := abs_nonneg _
    have hsq : ((k:ℝ) - m) ^ 2 = a ^ 2 := (sq_abs _).symm
    rw [hsq]
    calc a ^ 2 * |B k m| ≤ a ^ 2 * (C * ((1 + a) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left (hdecay k m) (sq_nonneg a)
      _ = C * (a ^ 2 / (1 + a) ^ 5) := by ring
      _ ≤ C * ((1 + a) ^ 2 / (1 + a) ^ 5) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
      _ = C * ((1 + a) ^ 3)⁻¹ := by
          congr 1
          have : (0:ℝ) < 1 + a := by linarith
          field_simp
  calc ∑ m ∈ W, ((k:ℝ) - m) ^ 2 * |B k m|
      ≤ ∑ m ∈ W, C * ((1 + 1 * |((k - m : ℤ) : ℝ)|) ^ 3)⁻¹ :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = C * ∑ m ∈ W, ((1 + 1 * |((k - m : ℤ) : ℝ)|) ^ 3)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C * Z3 := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact sum_le_tsum_of_injOn (fun m => k - m) (fun x _ y _ hxy => by simpa using hxy)
          (fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _))
          (summable_profile one_pos (by norm_num))

/-! ## The weighted residual sum, from (ul-rate-resid-hybrid) -/

/-- `Ω_ε = Σ_{n ∈ ℤ} (1+ε|n|)^{-2}`. -/
noncomputable def Ωε (ε : ℝ) : ℝ := ∑' n : ℤ, ((1 + ε * |(n:ℝ)|) ^ 2)⁻¹

/-- `Z₂ = Σ_{n ∈ ℤ} (1+|n|)^{-2}`. -/
noncomputable def Z2 : ℝ := ∑' n : ℤ, ((1 + 1 * |(n:ℝ)|) ^ 2)⁻¹

theorem sum_ω_le (A : Finset ℤ) {ε : ℝ} (hε : 0 < ε) (j : ℤ) :
    ∑ k ∈ A, ω ε j k ≤ Ωε ε := by
  set g : ℤ → ℝ := fun n => ((1 + ε * |(n:ℝ)|) ^ 2)⁻¹
  have hpt : ∀ k, ω ε j k = g (k - j) := by
    intro k; simp only [ω, sw, g, inv_pow, Int.cast_sub]
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    have := mul_nonneg hε.le (abs_nonneg (n:ℝ))
    exact inv_nonneg.mpr (pow_nonneg (by linarith) _)
  rw [Finset.sum_congr rfl (fun k _ => hpt k)]
  exact sum_le_tsum_of_injOn (fun k => k - j) (fun x _ y _ hxy => by simpa using hxy) hg0
    (summable_profile hε le_rfl)

/-- The distance to the complement of `W = [j-L, j+L]`: `D_k = L + 1 - |k-j|`. -/
noncomputable def Dist (L : ℕ) (j k : ℤ) : ℝ := (L:ℝ) + 1 - |(k:ℝ) - j|

/-- Each value of `D_k` is taken at most twice on `W`, hence
`Σ_{k ∈ W} (1+D_k)^{-2} ≤ 2 Z₂`. -/
theorem sum_dist_le (L : ℕ) (j : ℤ) :
    ∑ k ∈ Finset.Icc (j - L) (j + L), ((1 + Dist L j k) ^ 2)⁻¹ ≤ 2 * Z2 := by
  set W := Finset.Icc (j - L) (j + L)
  set g : ℤ → ℝ := fun n => ((1 + 1 * |(n:ℝ)|) ^ 2)⁻¹
  have hg0 : ∀ n, 0 ≤ g n := fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _)
  have hgs : Summable g := summable_profile one_pos le_rfl
  have hφ : ∀ k ∈ W, ((1 + Dist L j k) ^ 2)⁻¹ = g ((L:ℤ) + 1 - |k - j|) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have habs : |k - j| ≤ (L:ℤ) := abs_le.mpr ⟨by linarith, by linarith⟩
    have hnn : (0:ℤ) ≤ (L:ℤ) + 1 - |k - j| := by linarith
    simp only [g, Dist]
    rw [Int.cast_nonneg.mpr hnn |> abs_of_nonneg]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hφ, ← Finset.sum_filter_add_sum_filter_not W (fun k => j ≤ k)]
  have h1 : ∑ k ∈ W.filter (fun k => j ≤ k), g ((L:ℤ) + 1 - |k - j|) ≤ Z2 := by
    apply sum_le_tsum_of_injOn (fun k => (L:ℤ) + 1 - |k - j|) _ hg0 hgs
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    simp only at hxy
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hxy
    linarith
  have h2 : ∑ k ∈ W.filter (fun k => ¬ j ≤ k), g ((L:ℤ) + 1 - |k - j|) ≤ Z2 := by
    apply sum_le_tsum_of_injOn (fun k => (L:ℤ) + 1 - |k - j|) _ hg0 hgs
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    simp only at hxy
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hxy
    linarith
  linarith

/-- Per-term comparison: `ω_k (1+D_k)^{-8} ≤ 4/(ε² L²) · (1+D_k)^{-2}` on `W`. -/
theorem ω_dist_le (L : ℕ) (hL : 2 ≤ L) (j k : ℤ) (hk : k ∈ Finset.Icc (j - L) (j + L))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹ ≤
      4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + Dist L j k) ^ 2)⁻¹ := by
  have hk' := Finset.mem_Icc.mp hk
  have hkR : |(k:ℝ) - j| ≤ L := by
    rw [abs_le]; constructor
    · have : ((j - L : ℤ):ℝ) ≤ k := by exact_mod_cast hk'.1
      push_cast at this; linarith
    · have : (k:ℝ) ≤ ((j + L : ℤ):ℝ) := by exact_mod_cast hk'.2
      push_cast at this; linarith
  set a := |(k:ℝ) - j|
  have ha : 0 ≤ a := abs_nonneg _
  set D := Dist L j k
  have hD : D = (L:ℝ) + 1 - a := rfl
  have hD1 : 1 ≤ 1 + D := by rw [hD]; linarith
  have hLr : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hω : ω ε j k = ((1 + ε * a) ^ 2)⁻¹ := by simp only [ω, sw, inv_pow]; rfl
  have hp2 : 0 < (1 + D) ^ 2 := by positivity
  have hp8 : (1 + D) ^ 8 = (1 + D) ^ 6 * (1 + D) ^ 2 := by ring
  rw [hω, hp8, mul_inv]
  have hεL : 0 < ε ^ 2 * (L:ℝ) ^ 2 := by positivity
  by_cases hcase : a ≤ L / 2
  · -- inner half: `1 + D ≥ L/2`, so `(1+D)⁶ ≥ (1+D)² ≥ L²/4 ≥ ε² L²/4`
    have hbig : (L:ℝ) / 2 ≤ 1 + D := by rw [hD]; linarith
    have h6 : ε ^ 2 * (L:ℝ) ^ 2 ≤ 4 * (1 + D) ^ 6 := by
      have h1 : (L:ℝ) ^ 2 ≤ 4 * (1 + D) ^ 2 := by nlinarith
      have h2 : (1 + D) ^ 2 ≤ (1 + D) ^ 6 := by
        apply pow_le_pow_right₀ hD1; norm_num
      have h3 : ε ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (L:ℝ)]
    have hω1 : ((1 + ε * a) ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀; nlinarith [mul_nonneg hε.le ha]
    calc ((1 + ε * a) ^ 2)⁻¹ * (((1 + D) ^ 6)⁻¹ * ((1 + D) ^ 2)⁻¹)
        ≤ 1 * (((1 + D) ^ 6)⁻¹ * ((1 + D) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hω1 (by positivity)
      _ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + D) ^ 2)⁻¹ := by
          rw [one_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hεL]
          linarith
  · -- outer half: `ω_k ≤ 4/(ε² L²)` and `(1+D)^{-6} ≤ 1`
    push_neg at hcase
    have hω2 : ((1 + ε * a) ^ 2)⁻¹ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hεL]
      have : ε * (L / 2) ≤ 1 + ε * a := by nlinarith
      nlinarith [mul_pos hε (show (0:ℝ) < L / 2 by linarith)]
    have h6 : ((1 + D) ^ 6)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
    calc ((1 + ε * a) ^ 2)⁻¹ * (((1 + D) ^ 6)⁻¹ * ((1 + D) ^ 2)⁻¹)
        ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * (1 * ((1 + D) ^ 2)⁻¹) := by
          apply mul_le_mul hω2 _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + D) ^ 2)⁻¹ := by rw [one_mul]

/-- **Weighted residual sum.** On `W = [j-L, j+L]` with `L ≥ 2`, `0 < ε ≤ 1`, the hybrid
bound `|h_k| ≤ C_h (1/M + (1+D_k)^{-4})` of (ul-rate-resid-hybrid) gives
`Σ ω h² ≤ 2 C_h² (Ω_ε/M² + 8 Z₂/(ε² L²))`. -/
theorem residual_weighted_sum (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {M Ch : ℝ} (hM : 0 < M) (h : ℤ → ℝ)
    (hh : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |h k| ≤ Ch * (1 / M + ((1 + Dist L j k) ^ 4)⁻¹)) :
    ∑ k ∈ Finset.Icc (j - L) (j + L), ω ε j k * h k ^ 2 ≤
      2 * Ch ^ 2 * (Ωε ε / M ^ 2 + 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2)) := by
  set W := Finset.Icc (j - L) (j + L)
  have hsq : ∀ k ∈ W, h k ^ 2 ≤ 2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Dist L j k) ^ 8)⁻¹) := by
    intro k hk
    have hb := hh k hk
    have hx : 0 ≤ ((1 + Dist L j k) ^ 4)⁻¹ := by
      have hk' := Finset.mem_Icc.mp hk
      have : |(k:ℝ) - j| ≤ L := by
        rw [abs_le]; constructor
        · have : ((j - L : ℤ):ℝ) ≤ k := by exact_mod_cast hk'.1
          push_cast at this; linarith
        · have : (k:ℝ) ≤ ((j + L : ℤ):ℝ) := by exact_mod_cast hk'.2
          push_cast at this; linarith
      have : 0 ≤ 1 + Dist L j k := by simp only [Dist]; linarith
      positivity
    have h8 : (((1 + Dist L j k) ^ 4)⁻¹) ^ 2 = ((1 + Dist L j k) ^ 8)⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hM2 : (1 / M) ^ 2 = 1 / M ^ 2 := by rw [div_pow, one_pow]
    have habs : h k ^ 2 ≤ (Ch * (1 / M + ((1 + Dist L j k) ^ 4)⁻¹)) ^ 2 := by
      rw [← sq_abs (h k)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hM0 : 0 ≤ 1 / M := by positivity
    calc h k ^ 2 ≤ (Ch * (1 / M + ((1 + Dist L j k) ^ 4)⁻¹)) ^ 2 := habs
      _ ≤ 2 * Ch ^ 2 * ((1 / M) ^ 2 + (((1 + Dist L j k) ^ 4)⁻¹) ^ 2) := by
          nlinarith [sq_nonneg (1 / M - ((1 + Dist L j k) ^ 4)⁻¹), sq_nonneg Ch]
      _ = 2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Dist L j k) ^ 8)⁻¹) := by rw [h8, hM2]
  have hsplit : ∑ k ∈ W, ω ε j k * h k ^ 2 ≤
      2 * Ch ^ 2 * (1 / M ^ 2 * ∑ k ∈ W, ω ε j k +
        ∑ k ∈ W, ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹) := by
    calc ∑ k ∈ W, ω ε j k * h k ^ 2
        ≤ ∑ k ∈ W, ω ε j k * (2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Dist L j k) ^ 8)⁻¹)) :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hsq k hk) (ω_nonneg ε j k)
      _ = 2 * Ch ^ 2 * (1 / M ^ 2 * ∑ k ∈ W, ω ε j k +
            ∑ k ∈ W, ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hA : 1 / M ^ 2 * ∑ k ∈ W, ω ε j k ≤ Ωε ε / M ^ 2 := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (sum_ω_le W hε j) (by positivity)
  have hB : ∑ k ∈ W, ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹ ≤ 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) := by
    calc ∑ k ∈ W, ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹
        ≤ ∑ k ∈ W, 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + Dist L j k) ^ 2)⁻¹ :=
          Finset.sum_le_sum fun k hk => ω_dist_le L hL j k hk hε hε1
      _ = 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ∑ k ∈ W, ((1 + Dist L j k) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * (2 * Z2) :=
          mul_le_mul_of_nonneg_left (sum_dist_le L j) (by positivity)
      _ = 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) := by ring
  have h2C : 0 ≤ 2 * Ch ^ 2 := by positivity
  calc ∑ k ∈ W, ω ε j k * h k ^ 2
      ≤ 2 * Ch ^ 2 * (1 / M ^ 2 * ∑ k ∈ W, ω ε j k +
          ∑ k ∈ W, ω ε j k * ((1 + Dist L j k) ^ 8)⁻¹) := hsplit
    _ ≤ 2 * Ch ^ 2 * (Ωε ε / M ^ 2 + 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) h2C

/-- With a window of half-width `L ≥ c M`, the weighted residual sum is `O(M^{-2})`. -/
theorem residual_weighted_sum_rate (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {M Ch c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hLM : c * M ≤ L) (h : ℤ → ℝ)
    (hh : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |h k| ≤ Ch * (1 / M + ((1 + Dist L j k) ^ 4)⁻¹)) :
    ∑ k ∈ Finset.Icc (j - L) (j + L), ω ε j k * h k ^ 2 ≤
      2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)) / M ^ 2 := by
  have h0 := residual_weighted_sum j L hL hε hε1 hM h hh
  have hZ : 0 ≤ Z2 := tsum_nonneg fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _)
  have hcM : 0 < c * M := mul_pos hc hM
  have hL2 : (c * M) ^ 2 ≤ (L:ℝ) ^ 2 := pow_le_pow_left₀ hcM.le hLM 2
  have hfrac : 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) ≤ 8 * Z2 / (ε ^ 2 * c ^ 2) / M ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [sq_nonneg ε, mul_le_mul_of_nonneg_left hL2 (sq_nonneg ε)]
  calc ∑ k ∈ Finset.Icc (j - L) (j + L), ω ε j k * h k ^ 2
      ≤ 2 * Ch ^ 2 * (Ωε ε / M ^ 2 + 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2)) := h0
    _ ≤ 2 * Ch ^ 2 * (Ωε ε / M ^ 2 + 8 * Z2 / (ε ^ 2 * c ^ 2) / M ^ 2) := by
        gcongr
    _ = 2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)) / M ^ 2 := by ring

end UniformLanczos.Rate514

#print axioms UniformLanczos.Rate514.sw_sub_sq_le
#print axioms UniformLanczos.Rate514.quad_split
#print axioms UniformLanczos.Rate514.correction_lower
#print axioms UniformLanczos.Rate514.weighted_coercivity
#print axioms UniformLanczos.Rate514.energy_of_coercive
#print axioms UniformLanczos.Rate514.centre_le
#print axioms UniformLanczos.Rate514.centre_bound
#print axioms UniformLanczos.Rate514.summable_profile
#print axioms UniformLanczos.Rate514.row_moment_bound
#print axioms UniformLanczos.Rate514.sum_dist_le
#print axioms UniformLanczos.Rate514.ω_dist_le
#print axioms UniformLanczos.Rate514.residual_weighted_sum
#print axioms UniformLanczos.Rate514.residual_weighted_sum_rate
