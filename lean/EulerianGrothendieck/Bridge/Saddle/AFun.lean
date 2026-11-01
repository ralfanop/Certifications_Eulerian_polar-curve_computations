import Bridge.Saddle.Laplace
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Lemma 5.5, part 3: the Laplace transform `A(z) = ∫_{-1/2}^{1/2} e^{zt} dt` of the uniform law

Manuscript V173, eqs. (90) and (116).

* `hasDerivAt_Ak`: `A_k(z) = ∫ t^k e^{zt} dt` satisfies `A_k' = A_{k+1}`; `A = A_0` is entire;
* `A_eq_closed`: `A(z) = (e^{z/2} - e^{-z/2})/z` for `z ≠ 0` (eq. (90)), `A_zero`;
* `A_ofReal`, `one_le_Ar`, `Ar_le`: on the real axis `A = A_r` with `1 ≤ A_r(s) ≤ e^{|s|/2}`;
* `norm_A_le_Ar`: `|A(z)| ≤ A_r(Re z)`; `norm_A_decay`: `|A(z)| ≤ 2e^{|Re z|/2}/|z|` (eq. (116));
* `norm_A_sub`: `|A(z) - A(s)| ≤ e^{|s|/2} |z - s|` for `|z - s| ≤ 1`;
* `norm_A_lt`: `|A(s + iu)| < A_r(s)` for `u ≠ 0`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Interval

namespace EulerianBridge.Saddle

/-- `A_k(z) = ∫_{-1/2}^{1/2} t^k e^{zt} dt`. -/
noncomputable def Ak (k : ℕ) (z : ℂ) : ℂ := ∫ t in (-1/2:ℝ)..(1/2), (t:ℂ) ^ k * cexp (z * t)

theorem Ak_zero_eq : Ak 0 = A := by funext z; simp [Ak, A]

theorem abs_le_half_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι (-1/2:ℝ) (1/2)) : |t| ≤ 1/2 := by
  rw [uIoc_of_le (by norm_num)] at ht
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

theorem hasDerivAt_Ak (k : ℕ) (z : ℂ) : HasDerivAt (Ak k) (Ak (k + 1) z) z := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1/2) (b := 1/2) (x₀ := z) (ε := 1)
    (F := fun x (t:ℝ) => (t:ℂ) ^ k * cexp (x * t))
    (F' := fun x (t:ℝ) => (t:ℂ) ^ (k + 1) * cexp (x * t))
    (bound := fun _ => Real.exp (‖z‖ + 1)) one_pos
    (Eventually.of_forall (fun x => (by fun_prop : Continuous fun t : ℝ =>
      (t:ℂ) ^ k * cexp (x * t)).aestronglyMeasurable))
    ((by fun_prop : Continuous fun t : ℝ => (t:ℂ) ^ k * cexp (z * t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => (t:ℂ) ^ (k + 1) * cexp (z * t)).aestronglyMeasurable)
    (Eventually.of_forall (fun t ht x hx => ?_)) intervalIntegrable_const
    (Eventually.of_forall (fun t _ x _ => ?_))
  · exact key.2
  · have ht' := abs_le_half_of_mem_uIoc ht
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have h1 : |t| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (by linarith)
    have hx' : ‖x‖ < ‖z‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x z
      rw [mem_ball, dist_eq_norm] at hx
      linarith
    have h2 : (x * (t:ℂ)).re ≤ ‖z‖ + 1 := by
      calc (x * (t:ℂ)).re ≤ ‖x * (t:ℂ)‖ := Complex.re_le_norm _
        _ = ‖x‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ ‖z‖ + 1 := by linarith
    calc |t| ^ (k + 1) * Real.exp (x * (t:ℂ)).re ≤ 1 * Real.exp (‖z‖ + 1) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le zero_le_one
      _ = Real.exp (‖z‖ + 1) := one_mul _
  · have h := ((hasDerivAt_id x).mul_const (t:ℂ)).cexp.const_mul ((t:ℂ) ^ k)
    convert h using 1
    simp only [id, one_mul]; ring

theorem hasDerivAt_A (z : ℂ) : HasDerivAt A (Ak 1 z) z := by
  have := hasDerivAt_Ak 0 z; rwa [Ak_zero_eq] at this

theorem differentiable_A : Differentiable ℂ A := fun z => (hasDerivAt_A z).differentiableAt

theorem continuous_A : Continuous A := differentiable_A.continuous

theorem A_zero : A 0 = 1 := by simp [A]; norm_num

theorem A_eq_closed {z : ℂ} (hz : z ≠ 0) : A z = (cexp (z / 2) - cexp (-z / 2)) / z := by
  rw [A, integral_exp_mul_complex hz]
  congr 2 <;> push_cast <;> ring_nf

/-- The real Laplace transform `A_r(s) = ∫_{-1/2}^{1/2} e^{st} dt`. -/
noncomputable def Ar (s : ℝ) : ℝ := ∫ t in (-1/2:ℝ)..(1/2), Real.exp (s * t)

theorem A_ofReal (s : ℝ) : A s = (Ar s : ℂ) := by
  simp only [A, Ar]
  rw [← intervalIntegral.integral_ofReal]
  congr 1; funext t; push_cast; rfl

theorem one_le_Ar (s : ℝ) : 1 ≤ Ar s := by
  have hlin : ∫ t in (-1/2:ℝ)..(1/2), (1 + s * t) = 1 := by
    have h := intervalIntegral.integral_add (μ := volume) (a := (-1/2:ℝ)) (b := 1/2)
      (f := fun _ => (1:ℝ)) (g := fun t => s * t) intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ => s * t).intervalIntegrable _ _)
    rw [h, intervalIntegral.integral_const_mul, integral_id]
    norm_num
  rw [← hlin]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun t : ℝ => 1 + s * t).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (s * t)).intervalIntegrable _ _)
  intro t _
  show 1 + s * t ≤ Real.exp (s * t)
  linarith [Real.add_one_le_exp (s * t)]

theorem Ar_pos (s : ℝ) : 0 < Ar s := lt_of_lt_of_le one_pos (one_le_Ar s)

theorem Ar_le (s : ℝ) : Ar s ≤ Real.exp (|s| / 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1/2:ℝ)) (b := 1/2)
    (C := Real.exp (|s| / 2)) (f := fun t => Real.exp (s * t)) (fun t ht => by
      have ht' := abs_le_half_of_mem_uIoc ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc s * t ≤ |s * t| := le_abs_self _
        _ = |s| * |t| := abs_mul _ _
        _ ≤ |s| * (1/2) := mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
        _ = |s| / 2 := by ring)
  rw [Real.norm_eq_abs] at h
  have : |(1/2:ℝ) - (-1/2)| = 1 := by norm_num
  rw [this, mul_one] at h
  exact (le_abs_self _).trans h

theorem norm_A_le_Ar (z : ℂ) : ‖A z‖ ≤ Ar z.re := by
  rw [A]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
  rw [Ar]; congr 1; funext t
  rw [Complex.norm_exp]; congr 1; simp

theorem norm_A_decay {z : ℂ} (hz : z ≠ 0) : ‖A z‖ ≤ 2 * Real.exp (|z.re| / 2) / ‖z‖ := by
  rw [A_eq_closed hz, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖cexp (z / 2) - cexp (-z / 2)‖ ≤ ‖cexp (z / 2)‖ + ‖cexp (-z / 2)‖ := norm_sub_le _ _
    _ = Real.exp (z.re / 2) + Real.exp (-z.re / 2) := by
        rw [Complex.norm_exp, Complex.norm_exp]; congr 2 <;> simp
    _ ≤ Real.exp (|z.re| / 2) + Real.exp (|z.re| / 2) := by
        gcongr
        · linarith [le_abs_self z.re]
        · linarith [neg_abs_le z.re]
    _ = 2 * Real.exp (|z.re| / 2) := by ring

theorem norm_A_sub (s : ℝ) {z : ℂ} (h : ‖z - s‖ ≤ 1) :
    ‖A z - A s‖ ≤ Real.exp (|s| / 2) * ‖z - s‖ := by
  have hint : ∀ c : ℂ, IntervalIntegrable (fun t : ℝ => cexp (c * t)) volume (-1/2) (1/2) :=
    fun c => (by fun_prop : Continuous fun t : ℝ => cexp (c * t)).intervalIntegrable _ _
  rw [A, A, ← intervalIntegral.integral_sub (hint z) (hint s)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1/2:ℝ)) (b := 1/2)
    (C := Real.exp (|s| / 2) * ‖z - s‖) (f := fun t : ℝ => cexp (z * t) - cexp ((s:ℂ) * t))
    (fun t ht => by
      have ht' := abs_le_half_of_mem_uIoc ht
      have hfac : cexp (z * t) - cexp ((s:ℂ) * t) = cexp ((s:ℂ) * t) * (cexp ((z - s) * t) - 1) := by
        rw [mul_sub, ← Complex.exp_add]; ring_nf
      show ‖cexp (z * t) - cexp ((s:ℂ) * t)‖ ≤ _
      rw [hfac, norm_mul, Complex.norm_exp]
      have hn : ‖(z - s) * (t:ℂ)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        nlinarith [norm_nonneg (z - s), abs_nonneg t]
      have h1 := Complex.norm_exp_sub_one_le hn
      have h2 : ‖(z - s) * (t:ℂ)‖ ≤ ‖z - s‖ / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        nlinarith [norm_nonneg (z - s), abs_nonneg t]
      have h3 : Real.exp ((s:ℂ) * (t:ℂ)).re ≤ Real.exp (|s| / 2) := by
        apply Real.exp_le_exp.mpr
        have : ((s:ℂ) * (t:ℂ)).re = s * t := by simp
        rw [this]
        calc s * t ≤ |s * t| := le_abs_self _
          _ = |s| * |t| := abs_mul _ _
          _ ≤ |s| * (1/2) := mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
          _ = |s| / 2 := by ring
      calc Real.exp ((s:ℂ) * (t:ℂ)).re * ‖cexp ((z - s) * t) - 1‖
          ≤ Real.exp (|s| / 2) * (2 * (‖z - s‖ / 2)) :=
            mul_le_mul h3 (h1.trans (by linarith)) (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (|s| / 2) * ‖z - s‖ := by ring)
  have : |(1/2:ℝ) - (-1/2)| = 1 := by norm_num
  rw [this, mul_one] at hb
  exact hb

/-- `|e^{w/2} - e^{-w/2}|² = (e^{a} - e^{-a})² + 4 sin² b` for `w = 2a + 2bi`. -/
theorem normSq_exp_sub (s u : ℝ) :
    Complex.normSq (cexp (((s:ℂ) + u * I) / 2) - cexp (-((s:ℂ) + u * I) / 2)) =
      (Real.exp (s / 2) - Real.exp (-s / 2)) ^ 2 + 4 * Real.sin (u / 2) ^ 2 := by
  rw [Complex.normSq_apply]
  have hre1 : (((s:ℂ) + u * I) / 2).re = s / 2 := by simp
  have him1 : (((s:ℂ) + u * I) / 2).im = u / 2 := by simp
  have hre2 : (-((s:ℂ) + u * I) / 2).re = -s / 2 := by simp; try ring
  have him2 : (-((s:ℂ) + u * I) / 2).im = -(u / 2) := by simp; try ring
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im, hre1, him1, hre2,
    him2, Real.cos_neg, Real.sin_neg]
  have hee : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by
    rw [← Real.exp_add]; simp [show s / 2 + -s / 2 = 0 by ring]
  have hsc := Real.sin_sq_add_cos_sq (u / 2)
  linear_combination (Real.exp (s / 2) ^ 2 + Real.exp (-s / 2) ^ 2 - 2) * hsc +
    (2 - 2 * Real.cos (u / 2) ^ 2 + 2 * Real.sin (u / 2) ^ 2) * hee

theorem Ar_eq_closed {s : ℝ} (hs : s ≠ 0) : Ar s = (Real.exp (s / 2) - Real.exp (-s / 2)) / s := by
  have h := A_eq_closed (z := (s:ℂ)) (by exact_mod_cast hs)
  rw [A_ofReal] at h
  have h2 : ((Real.exp (s / 2) - Real.exp (-s / 2)) / s : ℝ) =
      (cexp ((s:ℂ) / 2) - cexp (-(s:ℂ) / 2)) / (s:ℂ) := by push_cast; ring_nf
  exact_mod_cast h.trans h2.symm

theorem sq_le_exp_sub_sq (s : ℝ) : s ^ 2 ≤ (Real.exp (s / 2) - Real.exp (-s / 2)) ^ 2 := by
  have hsh : Real.exp (s / 2) - Real.exp (-s / 2) = 2 * Real.sinh (s / 2) := by
    rw [Real.sinh_eq]; ring
  rw [hsh]
  rcases le_or_lt 0 s with h | h
  · have := Real.self_le_sinh_iff.mpr (show 0 ≤ s / 2 by linarith)
    nlinarith
  · have := Real.sinh_le_self_iff.mpr (show s / 2 ≤ 0 by linarith)
    nlinarith

/-- Strict contraction: `|A(s + iu)| < A_r(s)` for `u ≠ 0`. -/
theorem norm_A_lt (s : ℝ) {u : ℝ} (hu : u ≠ 0) : ‖A ((s:ℂ) + u * I)‖ < Ar s := by
  set z : ℂ := (s:ℂ) + u * I
  have hz : z ≠ 0 := by
    intro h; apply hu; have := congrArg Complex.im h; simpa [z] using this
  have hnz : ‖z‖ ^ 2 = s ^ 2 + u ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]; ring
  have hA2 : ‖A z‖ ^ 2 = ((Real.exp (s / 2) - Real.exp (-s / 2)) ^ 2 + 4 * Real.sin (u / 2) ^ 2) /
      (s ^ 2 + u ^ 2) := by
    rw [A_eq_closed hz, norm_div, div_pow, hnz, ← Complex.normSq_eq_norm_sq, normSq_exp_sub]
  have hsin := Real.sin_sq_lt_sq (show u / 2 ≠ 0 by positivity)
  have hpos : 0 < s ^ 2 + u ^ 2 := by positivity
  have hD := sq_le_exp_sub_sq s
  rw [← abs_of_pos (Ar_pos s), ← abs_norm, ← sq_lt_sq, hA2, div_lt_iff₀ hpos]
  by_cases hs : s = 0
  · subst hs
    have : Ar 0 = 1 := by simp [Ar]; norm_num
    rw [this]; simp; nlinarith
  · rw [Ar_eq_closed hs, div_pow]
    have hs2 : 0 < s ^ 2 := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ hs2]
    nlinarith [mul_lt_mul_of_pos_left hsin hs2]

end EulerianBridge.Saddle
