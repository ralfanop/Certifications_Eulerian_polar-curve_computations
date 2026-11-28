import SpecialImaginaryPoint.Section89Certificate

open Filter Topology Finset
open scoped Real
noncomputable section

namespace Manuscript14Eq211
open Manuscript14Section89

/-- The nested radicals in Proposition 8.6, indexed from zero. -/
def a (n : ℕ) : ℝ := Real.sqrtTwoAddSeries 0 n

theorem norm_z0_eq_b : ‖z0‖ = b := by
  rw [z0_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos b_pos]

def rawTail (m : ℕ) : ℝ := ∏ k ∈ Finset.range m, a (k + 3)

theorem tail_index (N : ℕ) :
    rawTail (N - 2) = ∏ n ∈ Finset.Icc 3 N, a n := by
  unfold rawTail
  refine Finset.prod_bij (fun k _ => k + 3) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 3, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

theorem shifted_cos (m : ℕ) :
    Real.cos ((π / 2) / 2 ^ (m + 2 + 1)) = a (m + 3) / 2 := by
  unfold a
  rw [a_eq_cos]
  rw [show m + 3 + 1 = (m + 2 + 1) + 1 by omega, pow_succ]
  ring

/-- Extract both initial factors and retain the correct power of two. -/
theorem shifted_product (m : ℕ) :
    (∏ k ∈ Finset.range (m + 2), Real.cos ((π / 2) / 2 ^ (k + 1))) =
      b * muHex * (1 / (2 : ℝ) ^ (m + 1) * rawTail m) := by
  induction m with
  | zero =>
    change (∏ k ∈ Finset.range (1 + 1), Real.cos ((π / 2) / 2 ^ (k + 1))) =
      b * muHex * (1 / (2 : ℝ) ^ (0 + 1) * rawTail 0)
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, viete_factors.1, viete_factors.2]
    simp [rawTail] <;> ring
  | succ m ih =>
    rw [show m.succ + 2 = (m + 2) + 1 by omega, Finset.prod_range_succ,
      ih, shifted_cos m]
    have ht : rawTail m.succ = rawTail m * a (m + 3) := by
      simp only [rawTail, Finset.prod_range_succ]
    rw [ht, show m.succ + 1 = (m + 1) + 1 by omega, pow_succ]
    have hp : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
    field_simp [hp] <;> ring

/-- Exact finite identity with the manuscript's inclusive bounds and denominator. -/
theorem eq211_finite (N : ℕ) (hN : 2 ≤ N) :
    (∏ k ∈ Finset.range N, Real.cos ((π / 2) / 2 ^ (k + 1))) =
      ‖z0‖ * muHex * (1 / (2 : ℝ) ^ (N - 1) *
        ∏ n ∈ Finset.Icc 3 N, a n) := by
  have h := shifted_product (N - 2)
  rw [show N - 2 + 2 = N by omega, show N - 2 + 1 = N - 1 by omega,
    tail_index N] at h
  rw [norm_z0_eq_b]
  exact h

/-- The weighted normalized product converges to 2/pi. -/
theorem eq211_weighted_limit :
    Tendsto (fun N : ℕ => ‖z0‖ * muHex * (1 / (2 : ℝ) ^ (N - 1) *
      ∏ n ∈ Finset.Icc 3 N, a n)) atTop (𝓝 (2 / π)) := by
  refine viete_tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact eq211_finite N hN

/-- The limit inside the parentheses of the corrected equation exists. -/
theorem eq211_inner_limit :
    Tendsto (fun N : ℕ => 1 / (2 : ℝ) ^ (N - 1) *
      ∏ n ∈ Finset.Icc 3 N, a n) atTop
      (𝓝 ((‖z0‖ * muHex)⁻¹ * (2 / π))) := by
  have hc : ‖z0‖ * muHex ≠ 0 := by
    rw [norm_z0_eq_b]
    apply mul_ne_zero b_ne_zero
    unfold muHex
    positivity
  refine (eq211_weighted_limit.const_mul ((‖z0‖ * muHex)⁻¹)).congr (fun n => ?_)
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem profile_pi : rEr π = 2 / π := by
  simp [rEr, Real.sin_pi_div_two]

/-- Exact equality of the outside prefactor times the inner limit with r_E(pi). -/
theorem eq211_prefactor :
    ‖z0‖ * muHex * ((‖z0‖ * muHex)⁻¹ * (2 / π)) = rEr π := by
  have hc : ‖z0‖ * muHex ≠ 0 := by
    rw [norm_z0_eq_b]
    apply mul_ne_zero b_ne_zero
    unfold muHex
    positivity
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, profile_pi]

#print axioms norm_z0_eq_b
#print axioms tail_index
#print axioms shifted_cos
#print axioms shifted_product
#print axioms eq211_finite
#print axioms eq211_weighted_limit
#print axioms eq211_inner_limit
#print axioms profile_pi
#print axioms eq211_prefactor

end Manuscript14Eq211
