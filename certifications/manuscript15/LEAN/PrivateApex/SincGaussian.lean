import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! PRIVATE: Gaussian domination of sinc proved by elementary derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PrivateApex
open Real Set Filter Topology

theorem sin_sub_mul_cos_nonneg {x : ℝ} (hx : x ∈ Icc 0 π) :
    0 ≤ sin x - x * cos x := by
  have hd (y : ℝ) : HasDerivAt (fun x : ℝ => sin x - x * cos x) (y * sin y) y := by
    convert (hasDerivAt_sin y).sub ((hasDerivAt_id' y).mul (hasDerivAt_cos y)) using 1 <;> ring
  have hm : MonotoneOn (fun x : ℝ => sin x - x * cos x) (Icc 0 π) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 π)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    exact mul_nonneg hy.1.le (sin_nonneg_of_nonneg_of_le_pi hy.1.le hy.2.le)
  simpa using hm (show 0 ∈ Icc (0 : ℝ) π from ⟨le_rfl, pi_pos.le⟩) hx hx.1

theorem sinc_gaussian_wronskian {x : ℝ} (hx : x ∈ Icc 0 π) :
    0 ≤ (1 - x ^ 2 / 3) * sin x - x * cos x := by
  have hd (y : ℝ) : HasDerivAt
      (fun x : ℝ => (1 - x ^ 2 / 3) * sin x - x * cos x)
      (y / 3 * (sin y - y * cos y)) y := by
    convert (((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 3)).mul
      (hasDerivAt_sin y)).sub ((hasDerivAt_id' y).mul (hasDerivAt_cos y)) using 1 <;>
      (try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply]) <;> ring
  have hm : MonotoneOn (fun x : ℝ => (1 - x ^ 2 / 3) * sin x - x * cos x) (Icc 0 π) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 π)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    exact mul_nonneg (div_nonneg hy.1.le (by norm_num)) (sin_sub_mul_cos_nonneg ⟨hy.1.le, hy.2.le⟩)
  simpa using hm (show 0 ∈ Icc (0 : ℝ) π from ⟨le_rfl, pi_pos.le⟩) hx hx.1

theorem gaussian_sinc_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => exp (y ^ 2 / 6) * sinc y)
      (exp (x ^ 2 / 6) * (x * cos x - (1 - x ^ 2 / 3) * sin x) / x ^ 2) x := by
  have hd := (((hasDerivAt_pow 2 x).div_const 6).exp).mul
    ((hasDerivAt_sin x).div (hasDerivAt_id' x) hx)
  have he : (fun y : ℝ => exp (y ^ 2 / 6) * sinc y) =ᶠ[𝓝 x]
      (fun y : ℝ => exp (y ^ 2 / 6) * (sin y / y)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [sinc_of_ne_zero hy]
  convert hd.congr_of_eventuallyEq he using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.div_apply]
  field_simp [hx]
  <;> ring

theorem sinc_le_gaussian {x : ℝ} (hx : x ∈ Icc 0 π) :
    sinc x ≤ exp (-(x ^ 2 / 6)) := by
  have hm : AntitoneOn (fun y : ℝ => exp (y ^ 2 / 6) * sinc y) (Icc 0 π) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 π)
      (by fun_prop)
    · intro y hy
      rw [interior_Icc] at hy
      exact (gaussian_sinc_hasDerivAt (ne_of_gt hy.1)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(gaussian_sinc_hasDerivAt (ne_of_gt hy.1)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
      linarith [sinc_gaussian_wronskian ⟨hy.1.le, hy.2.le⟩]
  have hg : exp (x ^ 2 / 6) * sinc x ≤ 1 := by
    simpa using hm (show 0 ∈ Icc (0 : ℝ) π from ⟨le_rfl, pi_pos.le⟩) hx hx.1
  calc
    sinc x = exp (-(x ^ 2 / 6)) * (exp (x ^ 2 / 6) * sinc x) := by
      rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
    _ ≤ exp (-(x ^ 2 / 6)) * 1 := mul_le_mul_of_nonneg_left hg (exp_pos _).le
    _ = _ := mul_one _

theorem abs_sinc_le_gaussian {x : ℝ} (hx : x ∈ Icc 0 π) :
    |sinc x| ≤ exp (-(x ^ 2 / 6)) := by
  have hs : 0 ≤ sinc x := by
    by_cases hz : x = 0
    · simp [hz]
    rw [sinc_of_ne_zero hz]
    exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2) hx.1
  rw [abs_of_nonneg hs]
  exact sinc_le_gaussian hx

#print axioms sin_sub_mul_cos_nonneg
#print axioms sinc_gaussian_wronskian
#print axioms gaussian_sinc_hasDerivAt
#print axioms sinc_le_gaussian
#print axioms abs_sinc_le_gaussian
end PrivateApex
