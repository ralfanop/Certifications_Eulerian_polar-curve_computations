import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Lemma 5.5, part 5: Cauchy estimates and Taylor remainders for holomorphic functions

If `f` is holomorphic on the closed disc `|z - c| ≤ R` and `|f| ≤ B` there, then
* `cauchy_coeff_bound`: `|f^{(n)}(c)| / n! ≤ B / R^n`;
* `taylor_remainder_bound`: `|f(c + w) - Σ_{n<N} f^{(n)}(c) w^n / n!| ≤ 2B (|w|/R)^N` for `|w| ≤ R/2`.
These are the estimates used for the Taylor expansion (73) of `Ψ` in the proof of Lemma 5.5.
-/

open Complex Metric Set Filter Topology
open scoped Nat NNReal

namespace EulerianBridge.Saddle

theorem cauchy_coeff_bound {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hB : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) (n : ℕ) :
    ‖((n ! : ℂ))⁻¹ * iteratedDeriv n f c‖ ≤ B / R ^ n := by
  lift R to ℝ≥0 using hR.le
  have hR' : (0:ℝ≥0) < R := by exact_mod_cast hR
  have hp := hf.hasFPowerSeriesOnBall hR'
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfac
  rw [← hfac, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero),
    one_mul]
  have h1 := (cauchyPowerSeries f c R n).le_opNorm (fun _ => (1:ℂ))
  simp only [norm_one, Finset.prod_const_one, mul_one] at h1
  refine h1.trans ((norm_cauchyPowerSeries_le f c R n).trans ?_)
  have hint : ∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap c R θ)‖ ≤ 2 * Real.pi * B := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 2 * Real.pi)
      (C := B) (f := fun θ => ‖f (circleMap c R θ)‖) (fun θ _ => by
        rw [norm_norm]
        apply hB
        rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero]
        simp)
    rw [Real.norm_eq_abs] at this
    have h2 : |2 * Real.pi - 0| = 2 * Real.pi := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
    rw [h2] at this
    linarith [le_abs_self (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap c R θ)‖)]
  have hRabs : |(R:ℝ)| = R := abs_of_nonneg R.2
  rw [hRabs, inv_pow, div_eq_mul_inv]
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hRn : 0 ≤ ((R:ℝ) ^ n)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap c R θ)‖) * ((R:ℝ) ^ n)⁻¹
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * B) * ((R:ℝ) ^ n)⁻¹ := by gcongr
    _ = B * ((R:ℝ) ^ n)⁻¹ := by field_simp

theorem norm_iteratedDeriv_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hB : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) (n : ℕ) :
    ‖iteratedDeriv n f c‖ ≤ n ! * (B / R ^ n) := by
  have h := cauchy_coeff_bound hR hf hB n
  rw [norm_mul, norm_inv, Complex.norm_natCast] at h
  have hn : (0:ℝ) < n ! := by exact_mod_cast n.factorial_pos
  rw [inv_mul_le_iff₀ hn] at h
  exact h

theorem taylor_remainder_bound {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hB : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) (N : ℕ)
    {w : ℂ} (hw : ‖w‖ ≤ R / 2) :
    ‖f (c + w) - ∑ n ∈ Finset.range N, ((n ! : ℂ))⁻¹ * iteratedDeriv n f c * w ^ n‖ ≤
      2 * B * (‖w‖ / R) ^ N := by
  have hz : c + w ∈ ball c R := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball (hf.mono ball_subset_closedBall) hz
  simp only [add_sub_cancel_left, smul_eq_mul] at hsum
  set a : ℕ → ℂ := fun n => ((n ! : ℂ))⁻¹ * (w ^ n * iteratedDeriv n f c)
  have htail := (hasSum_nat_add_iff' N).mpr hsum
  set q : ℝ := ‖w‖ / R
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; linarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left (B * q ^ N)
  have hB0 : 0 ≤ B := by
    have := hB c (mem_closedBall_self hR.le); exact (norm_nonneg _).trans this
  have hbd : ∀ n, ‖a (n + N)‖ ≤ B * q ^ N * q ^ n := by
    intro n
    have hc := cauchy_coeff_bound hR hf hB (n + N)
    calc ‖a (n + N)‖ = ‖((((n + N) ! : ℂ))⁻¹ * iteratedDeriv (n + N) f c)‖ * ‖w‖ ^ (n + N) := by
          simp only [a, norm_mul, norm_pow]; ring
      _ ≤ B / R ^ (n + N) * ‖w‖ ^ (n + N) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = B * q ^ N * q ^ n := by
          simp only [q, div_pow, pow_add]; field_simp
  have hle := htail.norm_le_of_bounded hgeo hbd
  have hsum_eq : ∑ i ∈ Finset.range N, a i =
      ∑ n ∈ Finset.range N, ((n ! : ℂ))⁻¹ * iteratedDeriv n f c * w ^ n := by
    apply Finset.sum_congr rfl; intro n _; simp only [a]; ring
  rw [hsum_eq] at hle
  refine hle.trans ?_
  have : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc B * q ^ N * (1 - q)⁻¹ ≤ B * q ^ N * 2 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * B * q ^ N := by ring

end EulerianBridge.Saddle
