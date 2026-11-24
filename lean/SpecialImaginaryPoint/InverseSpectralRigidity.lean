import Mathlib

/-! Eulerian Dyadic Spectral Rigidity and Optimal Finite-Data Reconstruction.
Stage 1: exact dyadic iteration, stability, and rational localization budget.
The abstract sequence theorems do not assume spectral or Fisher realizability.
Analytic and operator bridges are tracked separately. -/
namespace M14.InverseSpectralRigidity

open scoped BigOperators
open Filter

theorem dyadic_iteration (u d : ℕ → ℝ)
    (h : ∀ n, 4 * u n = u (n + 1) + d n) (N : ℕ) :
    u 0 = (∑ i ∈ Finset.range N, (1 / 4 : ℝ) ^ (i + 1) * d i) +
      (1 / 4 : ℝ) ^ N * u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hr : u N = (u (N + 1) + d N) / 4 := by
      linarith [h N]
    calc
      u 0 = (∑ i ∈ Finset.range N, (1 / 4 : ℝ) ^ (i + 1) * d i) +
          (1 / 4 : ℝ) ^ N * u N := ih
      _ = _ := by
        rw [Finset.sum_range_succ, hr, pow_succ]
        ring

theorem dyadic_step_bound (u d : ℕ → ℝ) (eps : ℝ)
    (h : ∀ n, 4 * u n = u (n + 1) + d n)
    (hd : ∀ n, |d n| ≤ eps) (m : ℕ) :
    |u m| ≤ (|u (m+1)| + eps) / 4 := by
  have ha : |4 * u m| ≤ |u (m+1)| + |d m| := by
    rw [h m]
    exact abs_add_le _ _
  rw [abs_mul] at ha
  norm_num at ha
  linarith [hd m]

theorem dyadic_finite_stability (u d : ℕ → ℝ) (eps : ℝ)
    (h : ∀ n, 4 * u n = u (n + 1) + d n)
    (hd : ∀ n, |d n| ≤ eps) (N m : ℕ) :
    |u m| ≤ eps / 3 * (1 - (1 / 4 : ℝ)^N) +
      (1 / 4 : ℝ)^N * |u (m+N)| := by
  induction N generalizing m with
  | zero => simp
  | succ N ih =>
    have hh := ih (m+1)
    rw [show m+1+N = m+(N+1) by omega] at hh
    have hs := dyadic_step_bound u d eps h hd m
    rw [pow_succ]
    linarith

theorem dyadic_stability_of_bounded (u d : ℕ → ℝ) (eps M : ℝ)
    (h : ∀ n, 4 * u n = u (n + 1) + d n)
    (hd : ∀ n, |d n| ≤ eps) (hu : ∀ n, |u n| ≤ M) :
    |u 0| ≤ eps / 3 := by
  have hq : Tendsto (fun n : ℕ => (1 / 4 : ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : Tendsto (fun n : ℕ => eps / 3 * (1 - (1 / 4 : ℝ)^n) +
      (1 / 4 : ℝ)^n * M) atTop (nhds (eps / 3)) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have he : Tendsto (fun _ : ℕ => eps / 3) atTop (nhds (eps / 3)) := tendsto_const_nhds
    have hm : Tendsto (fun _ : ℕ => M) atTop (nhds M) := tendsto_const_nhds
    have ht := (he.mul (h1.sub hq)).add (hq.mul hm)
    simpa using ht
  apply ge_of_tendsto hc
  exact Eventually.of_forall (fun n => by
    have hf := dyadic_finite_stability u d eps h hd n 0
    simp only [zero_add] at hf
    have hpow : 0 ≤ (1 / 4 : ℝ)^n :=
      pow_nonneg (by norm_num) n
    have hmul : (1 / 4 : ℝ)^n * |u n| ≤ (1 / 4 : ℝ)^n * M :=
      mul_le_mul_of_nonneg_left (hu n) hpow
    exact hf.trans (add_le_add_left hmul _))

theorem dyadic_rigidity_of_bounded (u : ℕ → ℝ) (M : ℝ)
    (h : ∀ n, 4 * u n = u (n + 1)) (hu : ∀ n, |u n| ≤ M) :
    u 0 = 0 := by
  have hb := dyadic_stability_of_bounded u (fun _ => 0) 0 M
    (fun n => by simpa using h n) (by simp) hu
  have hz : |u 0| ≤ 0 := by simpa using hb
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

theorem trace_stability (tr : ℝ) (eps : ℝ)
    (h : |6 * tr - 1| ≤ eps) : |tr - 1 / 6| ≤ eps / 6 := by
  have he : 6 * (tr - 1 / 6) = 6 * tr - 1 := by ring
  rw [← he, abs_mul] at h
  norm_num at h
  linarith

-- Exact rational part of the N=32, M=2, h=1, S=1/5 certificate.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem rational_budget :
    (162 : ℚ)^32 / 10^74 +
      6000 * (41 / 5 : ℚ)^33 / (Nat.factorial 33 : ℚ) < 3 / 2000 := by
  norm_num [Nat.factorial]

theorem rational_threshold :
    (3 : ℚ) / 2000 < (1 / 100 - (1 / 100)^3 / 6) / (63 / 10) := by
  norm_num

end M14.InverseSpectralRigidity

#print axioms M14.InverseSpectralRigidity.dyadic_iteration
#print axioms M14.InverseSpectralRigidity.dyadic_step_bound
#print axioms M14.InverseSpectralRigidity.dyadic_finite_stability
#print axioms M14.InverseSpectralRigidity.dyadic_stability_of_bounded
#print axioms M14.InverseSpectralRigidity.dyadic_rigidity_of_bounded
#print axioms M14.InverseSpectralRigidity.trace_stability
#print axioms M14.InverseSpectralRigidity.rational_budget
#print axioms M14.InverseSpectralRigidity.rational_threshold
