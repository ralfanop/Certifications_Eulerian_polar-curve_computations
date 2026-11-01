import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lemma 5.5, part 1: the centred cardinal B-spline density and its Laplace transform

Manuscript V173, Section 5, eqs. (71) and (87)–(90).

`w 1 = 1_{(-1/2,1/2]}` and `w (M+1) y = ∫_{-1/2}^{1/2} w M (y - t) dt` (convolution with the uniform law);
`w M` is the density of `S_M`. We prove
* `0 ≤ w M` and `w M y = 0` for `|y| > M/2` (start of the formalisation of Lemma 5.5).
-/

open MeasureTheory Set intervalIntegral Complex

namespace EulerianBridge.Saddle

/-- The centred cardinal B-spline density `w_M` (`M ≥ 1`); `w 0` is unused. -/
noncomputable def w : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => Set.indicator (Ioc (-1/2:ℝ) (1/2)) (fun _ => 1)
  | (M + 2) => fun y => ∫ t in (-1/2:ℝ)..(1/2), w (M + 1) (y - t)

/-- `A(z) = ∫_{-1/2}^{1/2} e^{zt} dt`. -/
noncomputable def A (z : ℂ) : ℂ := ∫ t in (-1/2:ℝ)..(1/2), cexp (z * t)

theorem w_succ_succ (M : ℕ) (y : ℝ) : w (M + 2) y = ∫ t in (-1/2:ℝ)..(1/2), w (M + 1) (y - t) := by
  simp [w]

theorem w_one_eq (y : ℝ) : w 1 y = if y ∈ Ioc (-1/2:ℝ) (1/2) then 1 else 0 := by
  simp [w, Set.indicator_apply]

theorem w_nonneg : ∀ (M : ℕ) (y : ℝ), 0 ≤ w M y
  | 0, _ => by simp [w]
  | 1, y => by rw [w_one_eq]; split_ifs <;> norm_num
  | (M + 2), y => by
      rw [w_succ_succ]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => w_nonneg (M + 1) (y - t))

theorem w_support : ∀ (M : ℕ), 1 ≤ M → ∀ y : ℝ, (M:ℝ) / 2 < |y| → w M y = 0
  | 0, h, _, _ => absurd h (by norm_num)
  | 1, _, y, hy => by
      rw [w_one_eq, if_neg]
      rintro ⟨h1, h2⟩
      rw [lt_abs] at hy
      push_cast at hy
      rcases hy with hy | hy <;> linarith
  | (M + 2), _, y, hy => by
      rw [w_succ_succ]
      apply intervalIntegral.integral_zero_ae
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le (by norm_num)] at ht
      apply w_support (M + 1) (by omega)
      push_cast at hy ⊢
      rw [lt_abs] at hy ⊢
      rcases hy with hy | hy
      · left; linarith [ht.2]
      · right; linarith [ht.1]

end EulerianBridge.Saddle
