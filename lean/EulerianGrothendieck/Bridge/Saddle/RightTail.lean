import Bridge.Saddle.Corollary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# M12 Lemma 5.6: actual cardinal B-spline on the final knot interval
Source: frozen 12.tex, label lem:ul-spline, lines 1507–1513.
Derive the exact local density from the existing convolution definition.
No Floater premise is used. Interior strict log-concavity is a separate goal.
-/

open MeasureTheory Set Filter Topology

namespace EulerianBridge.Saddle

theorem w_right_tail (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    w (n + 1) (((n + 1 : ℕ) : ℝ) / 2 - δ) = δ ^ n / (n.factorial : ℝ) := by
  induction n generalizing δ with
  | zero =>
    rw [w_one_eq, if_pos]
    · simp
    · constructor <;> push_cast <;> linarith
  | succ n ih =>
    let R : ℝ := ((n + 1 : ℕ) : ℝ) / 2
    have hR : ((n + 1 + 1 : ℕ) : ℝ) / 2 = R + 1 / 2 := by
      dsimp [R]
      push_cast
      ring
    rw [w_succ_primitive (n + 1) (by omega), hR]
    have ha : R + 1 / 2 - δ - 1 / 2 = R - δ := by ring
    have hb : R + 1 / 2 - δ + 1 / 2 = R + 1 - δ := by ring
    rw [ha, hb]
    have hI := intervalIntegrable_of_le_one (w_measurable (n + 1))
      (w_nonneg (n + 1)) (w_le_one (n + 1))
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI (R - δ) R) (hI R (R + 1 - δ))]
    have hz : (∫ t in R..(R + 1 - δ), w (n + 1) t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      refine Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le (by linarith : R ≤ R + 1 - δ)] at ht
      apply w_support (n + 1) (by omega)
      exact ht.1.trans_le (le_abs_self t)
    rw [hz, add_zero]
    have he : (∫ t in (R - δ)..R, w (n + 1) t) =
        ∫ t in (R - δ)..R, (R - t) ^ n / (n.factorial : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : R - δ ≤ R)] at ht
      have h := ih (R - t) (by linarith [ht.2]) (by linarith [ht.1])
      change w (n + 1) (R - (R - t)) = _ at h
      convert h using 2 <;> ring
    rw [he, intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n / (n.factorial : ℝ)) R]
    have ha' : R - R = 0 := by ring
    have hb' : R - (R - δ) = δ := by ring
    rw [ha', hb']
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ, Nat.cast_ofNat]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem w_right_tail_pos (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < w (n + 1) (((n + 1 : ℕ) : ℝ) / 2 - δ) := by
  rw [w_right_tail n δ hδ0.le hδ1]
  positivity

/-- Exact density of the scaled sum, on its final knot interval. -/
theorem gM_right_tail (n : ℕ) (x : ℝ) (h0 : 0 ≤ ((n + 1 : ℕ) : ℝ) * (1 / 2 - x))
    (h1 : ((n + 1 : ℕ) : ℝ) * (1 / 2 - x) < 1) :
    gM (n + 1) x =
      ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * (1 / 2 - x)) ^ n /
        (n.factorial : ℝ) := by
  unfold gM
  have harg : ((n + 1 : ℕ) : ℝ) * x =
      ((n + 1 : ℕ) : ℝ) / 2 - ((n + 1 : ℕ) : ℝ) * (1 / 2 - x) := by ring
  rw [harg, w_right_tail n _ h0 h1]
  ring

end EulerianBridge.Saddle

#print axioms EulerianBridge.Saddle.w_right_tail
#print axioms EulerianBridge.Saddle.w_right_tail_pos
#print axioms EulerianBridge.Saddle.gM_right_tail
