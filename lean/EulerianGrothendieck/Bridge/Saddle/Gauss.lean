import Bridge.AppendixAMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lemma 5.5, part 7: Gaussian moments and polynomial–Gaussian majorants

* `pow_one_add_sq_le`: `(1+z²)^N ≤ N! (2/c)^N e^{c/2} e^{cz²/2}`;
* `integrable_poly_gauss`: `(1+z²)^N e^{-cz²}` is integrable for `c > 0`;
* `integral_complex_moment`: `∫ (iz)^n e^{-κz²/2} dz = √(2π/κ) μ_n(κ)`, with
  `μ_{2k} = (-1)^k (2k-1)!! κ^{-k}` and `μ_{2k+1} = 0` (the moments used after (129));
* `bounded_pow_mul_geom`: `M^k ρ^M` is bounded for `0 ≤ ρ < 1` (exponential smallness).
-/

open MeasureTheory Set Complex Filter Topology Real
open scoped Nat

namespace EulerianBridge.Saddle

theorem abs_le_one_add_sq (z : ℝ) : |z| ≤ 1 + z ^ 2 := by
  nlinarith [sq_abs z, abs_nonneg z, sq_nonneg (|z| - 1)]

theorem pow_one_add_sq_le {c : ℝ} (hc : 0 < c) (N : ℕ) (z : ℝ) :
    (1 + z ^ 2) ^ N ≤ N ! * (2 / c) ^ N * Real.exp (c / 2) * Real.exp (c * z ^ 2 / 2) := by
  have hx : 0 ≤ c * (1 + z ^ 2) / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx N
  have hN : (0:ℝ) < N ! := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hN] at h
  have he : Real.exp (c * (1 + z ^ 2) / 2) = Real.exp (c / 2) * Real.exp (c * z ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he] at h
  have hpow : (c * (1 + z ^ 2) / 2) ^ N = (c / 2) ^ N * (1 + z ^ 2) ^ N := by
    rw [← mul_pow]; ring_nf
  rw [hpow] at h
  have hc2 : 0 < (c / 2) ^ N := by positivity
  have : (1 + z ^ 2) ^ N ≤ (Real.exp (c / 2) * Real.exp (c * z ^ 2 / 2) * N !) / (c / 2) ^ N := by
    rw [le_div_iff₀ hc2]; linarith
  refine this.trans (le_of_eq ?_)
  rw [div_pow, div_pow]
  have hcN : 0 < c ^ N := pow_pos hc N
  have h2N : 0 < (2:ℝ) ^ N := by positivity
  field_simp

theorem integrable_poly_gauss {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Integrable (fun z : ℝ => (1 + z ^ 2) ^ N * Real.exp (-c * z ^ 2)) := by
  set C := (N ! : ℝ) * (2 / c) ^ N * Real.exp (c / 2)
  have hg := (integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).const_mul C
  refine hg.mono' (by fun_prop) (Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := pow_one_add_sq_le hc N z
  calc (1 + z ^ 2) ^ N * Real.exp (-c * z ^ 2)
      ≤ (C * Real.exp (c * z ^ 2 / 2)) * Real.exp (-c * z ^ 2) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = C * Real.exp (-(c / 2) * z ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The real Gaussian moments `∫ z^{2k} e^{-κz²/2} dz = (2k-1)!! √(2π/κ) κ^{-k}`. -/
theorem integral_even_moment {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    ∫ z : ℝ, z ^ (2 * k) * Real.exp (-(κ * z ^ 2) / 2) =
      ((2 * k - 1 : ℕ)‼ : ℝ) * Real.sqrt (2 * π / κ) / κ ^ k := by
  have hg := EulerianBridge.AppendixA.gaussian_moment k
  rw [MeasureTheory.integral_div] at hg
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsub := Measure.integral_comp_mul_left
    (fun x : ℝ => x ^ (2 * k) * Real.exp (-x ^ 2 / 2)) (Real.sqrt κ)
  simp only at hsub
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hfun : (fun z : ℝ => (Real.sqrt κ * z) ^ (2 * k) * Real.exp (-(Real.sqrt κ * z) ^ 2 / 2)) =
      fun z => κ ^ k * (z ^ (2 * k) * Real.exp (-(κ * z ^ 2) / 2)) := by
    funext z
    rw [mul_pow, pow_mul, hsq, mul_pow, hsq]; ring_nf
  rw [hfun, MeasureTheory.integral_const_mul, abs_inv, abs_of_pos hs, smul_eq_mul] at hsub
  have hpi : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hval : ∫ x : ℝ, x ^ (2 * k) * Real.exp (-x ^ 2 / 2) = ((2 * k - 1 : ℕ)‼ : ℝ) * Real.sqrt (2 * π) := by
    field_simp at hg
    simp only [neg_div]; rw [hg]; ring
  rw [hval] at hsub
  have hk : 0 < κ ^ k := pow_pos hκ k
  rw [Real.sqrt_div' _ hκ.le]
  field_simp
  field_simp at hsub
  linarith

theorem integral_odd_moment (κ : ℝ) (k : ℕ) :
    ∫ z : ℝ, z ^ (2 * k + 1) * Real.exp (-(κ * z ^ 2) / 2) = 0 := by
  have h := integral_neg_eq_self (fun z : ℝ => z ^ (2 * k + 1) * Real.exp (-(κ * z ^ 2) / 2)) volume
  have hodd : (fun z : ℝ => (-z) ^ (2 * k + 1) * Real.exp (-(κ * (-z) ^ 2) / 2)) =
      fun z => -(z ^ (2 * k + 1) * Real.exp (-(κ * z ^ 2) / 2)) := by
    funext z; rw [Odd.neg_pow ⟨k, rfl⟩, neg_sq]; ring
  simp only [hodd, MeasureTheory.integral_neg] at h
  linarith

/-- The normalised moments `μ_n(κ)`: `μ_{2k} = (-1)^k (2k-1)!!/κ^k`, `μ_{2k+1} = 0`. -/
noncomputable def μ (κ : ℝ) (n : ℕ) : ℂ :=
  if Even n then ((-1) ^ (n / 2) * ((n - 1 : ℕ)‼ : ℝ) / κ ^ (n / 2) : ℝ) else 0

theorem integrable_complex_moment {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Integrable (fun z : ℝ => ((z:ℂ) * I) ^ n * (Real.exp (-(κ * z ^ 2) / 2) : ℂ)) := by
  have hb := integrable_poly_gauss (c := κ / 2) (by positivity) n
  refine hb.mono' (by fun_prop) (Eventually.of_forall (fun z => ?_))
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : |z| ^ n ≤ (1 + z ^ 2) ^ n := pow_le_pow_left₀ (abs_nonneg z) (abs_le_one_add_sq z) n
  calc |z| ^ n * Real.exp (-(κ * z ^ 2) / 2) ≤ (1 + z ^ 2) ^ n * Real.exp (-(κ * z ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 + z ^ 2) ^ n * Real.exp (-(κ / 2) * z ^ 2) := by ring_nf

theorem integral_complex_moment {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ∫ z : ℝ, ((z:ℂ) * I) ^ n * (Real.exp (-(κ * z ^ 2) / 2) : ℂ) =
      (Real.sqrt (2 * π / κ) : ℂ) * μ κ n := by
  have hfun : (fun z : ℝ => ((z:ℂ) * I) ^ n * (Real.exp (-(κ * z ^ 2) / 2) : ℂ)) =
      fun z => I ^ n * ((z ^ n * Real.exp (-(κ * z ^ 2) / 2) : ℝ) : ℂ) := by
    funext z; push_cast; ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_complex_ofReal]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk' : n = 2 * k := by omega
    subst hk'
    rw [integral_even_moment hκ k]
    have hev : Even (2 * k) := even_two_mul k
    simp only [μ, hev, if_true, show 2 * k / 2 = k by omega]
    rw [pow_mul, Complex.I_sq]
    push_cast; ring
  · subst hk
    rw [integral_odd_moment κ k]
    have hodd : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, rfl⟩
    simp [μ, hodd]

/-- `M^k ρ^M` is bounded for `0 ≤ ρ < 1`. -/
theorem bounded_pow_mul_geom {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (k : ℕ) :
    ∃ C, ∀ M : ℕ, (M:ℝ) ^ k * ρ ^ M ≤ C := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rwa [abs_of_nonneg h0])
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  exact ⟨C, fun M => hC ⟨M, rfl⟩⟩

end EulerianBridge.Saddle
