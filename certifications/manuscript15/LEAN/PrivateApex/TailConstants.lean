import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! PRIVATE: the manuscript's analytic majorant is strictly below two for every N≥73. -/
namespace PrivateApex
noncomputable section
open Real

def analyticMajorant (N : ℕ) : ℝ :=
  2 * sqrt (216 * (N : ℝ)^2 / (π * ((N : ℝ)+2)^3)) +
    8 * (N : ℝ) / (((N : ℝ)-1) * π^N)

theorem analyticMajorant_lt_two (N : ℕ) (hN : 73 ≤ N) : analyticMajorant N < 2 := by
  have hn : (73 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (0 : ℝ) < (N : ℝ)-1 := by linarith
  have hc : (N : ℝ)^3 ≤ ((N : ℝ)+2)^3 := by gcongr <;> linarith
  have hp : 3 * (N : ℝ)^3 ≤ π * ((N : ℝ)+2)^3 :=
    (mul_le_mul_of_nonneg_left hc (by norm_num)).trans
      (mul_le_mul_of_nonneg_right pi_gt_three.le (by positivity))
  have hr : 216 * (N : ℝ)^2 / (π * ((N : ℝ)+2)^3) ≤ 72 / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 72 by norm_num)]
  have hs : sqrt (216 * (N : ℝ)^2 / (π * ((N : ℝ)+2)^3)) < 199/200 := by
    apply (sqrt_lt' (by norm_num : (0 : ℝ) < 199/200)).mpr
    apply lt_of_le_of_lt hr
    apply lt_of_le_of_lt (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn)
    norm_num
  have hpow : (3 : ℝ)^73 ≤ π^N := by
    calc
      _ ≤ (3 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hN
      _ ≤ π^N := pow_le_pow_left₀ (by norm_num) pi_gt_three.le N
  have ht : 8 * (N : ℝ) / (((N : ℝ)-1)*π^N) < 1/100 := by
    calc
      _ ≤ 16 * ((N : ℝ)-1) / (((N : ℝ)-1)*π^N) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 16 / π^N := by field_simp
      _ ≤ 16 / (3 : ℝ)^73 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      _ < 1/100 := by norm_num
  unfold analyticMajorant
  linarith

#print axioms analyticMajorant_lt_two
end
end PrivateApex
