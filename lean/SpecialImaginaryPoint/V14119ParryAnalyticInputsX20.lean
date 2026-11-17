import Mathlib

/-! Actual high-order analytic Taylor inputs for M14 Prop. 10.2.
These are uniform estimates for sinh and log, not finite coefficient checks.
The subsequent polynomial composition/truncation and inverse estimates for
the actual P and -PC still need to be connected to these inputs. -/
namespace Manuscript14.ParryAnalyticInputs

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable def sinh25 (x : ℝ) : ℝ :=
    x ^ 1 / (Nat.factorial 1 : ℝ) +
    x ^ 3 / (Nat.factorial 3 : ℝ) +
    x ^ 5 / (Nat.factorial 5 : ℝ) +
    x ^ 7 / (Nat.factorial 7 : ℝ) +
    x ^ 9 / (Nat.factorial 9 : ℝ) +
    x ^ 11 / (Nat.factorial 11 : ℝ) +
    x ^ 13 / (Nat.factorial 13 : ℝ) +
    x ^ 15 / (Nat.factorial 15 : ℝ) +
    x ^ 17 / (Nat.factorial 17 : ℝ) +
    x ^ 19 / (Nat.factorial 19 : ℝ) +
    x ^ 21 / (Nat.factorial 21 : ℝ) +
    x ^ 23 / (Nat.factorial 23 : ℝ) +
    x ^ 25 / (Nat.factorial 25 : ℝ)

theorem sinh_taylor25 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sinh x - sinh25 x| ≤ x ^ 27 := by
  let P : ℝ := ∑ m ∈ Finset.range 27, x ^ m / (m.factorial : ℝ)
  let M : ℝ := ∑ m ∈ Finset.range 27, (-x) ^ m / (m.factorial : ℝ)
  let E : ℝ := |x| ^ 27 * (28 : ℝ) *
      ((((Nat.factorial 27 : ℕ) : ℝ) * 27)⁻¹)
  have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx]; exact hx1
  have hmabs : |-x| ≤ 1 := by simpa only [abs_neg] using hxabs
  have hp : |Real.exp x - P| ≤ E := by
    have h := Real.exp_bound (x := x) hxabs (n := 27) (by norm_num)
    simpa [P, E, div_eq_mul_inv, mul_assoc] using h
  have hm : |Real.exp (-x) - M| ≤ E := by
    have h := Real.exp_bound (x := -x) hmabs (n := 27) (by norm_num)
    simpa [M, E, abs_neg, div_eq_mul_inv, mul_assoc] using h
  have hd : |(Real.exp x - Real.exp (-x)) - (P - M)| ≤ 2 * E := by
    rcases abs_le.mp hp with ⟨hl1, hu1⟩
    rcases abs_le.mp hm with ⟨hl2, hu2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hf : (P - M) / 2 = sinh25 x := by
    dsimp [P, M, sinh25]
    norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring
  have he : Real.sinh x - sinh25 x =
      ((Real.exp x - Real.exp (-x)) - (P - M)) / 2 := by
    rw [Real.sinh_eq, ← hf]
    ring
  have hE : E ≤ x ^ 27 := by
    dsimp [E]
    rw [abs_of_nonneg hx]
    have hpos : 0 ≤ x^27 := pow_nonneg hx _
    norm_num [Nat.factorial] <;> linarith
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The actual quotient B(x²) has a degree-12 Taylor polynomial and a
uniform x^26 remainder on the positive unit interval. -/
theorem profile_taylor25 (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.sinh x / x - sinh25 x / x| ≤ x ^ 26 := by
  rw [← sub_div, abs_div, abs_of_pos hx]
  apply (div_le_iff₀ hx).2
  calc
    _ ≤ x ^ 27 := sinh_taylor25 x hx.le hx1
    _ = x ^ 26 * x := by ring

/-- The normalized numerator 6(B-1)/t has a uniform x^24 remainder.
Here the two singular divisions are by x and x², respectively. -/
theorem normalized_profile_taylor25 (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |6 * (Real.sinh x / x - 1) / x^2 -
      6 * (sinh25 x / x - 1) / x^2| ≤ 6 * x ^ 24 := by
  have h := profile_taylor25 x hx hx1
  rw [← sub_div]
  have he : 6 * (Real.sinh x / x - 1) - 6 * (sinh25 x / x - 1) =
      6 * (Real.sinh x / x - sinh25 x / x) := by ring
  rw [he, abs_div, abs_of_pos (sq_pos_of_pos hx), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply (div_le_iff₀ (sq_pos_of_pos hx)).2
  calc
    _ ≤ 6 * x^26 := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 6 * x^24 * x^2 := by ring

/-- General logarithm Taylor remainder, at every nonnegative y ≤ 1/2.
At n=12 this supplies the order-13 logarithm error needed for log B. -/
theorem log_one_add_taylor (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1/2) (n : ℕ) :
    |Real.log (1+y) + ∑ i ∈ Finset.range n, (-y)^(i+1) / ((i:ℝ)+1)| ≤
      2 * y^(n+1) := by
  have habs : |(-y)| < 1 := by rw [abs_neg, abs_of_nonneg hy]; linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) habs n
  simp only [sub_neg_eq_add, abs_neg, abs_of_nonneg hy] at h
  have hd : 0 < 1-y := by linarith
  have hp : 0 ≤ y^(n+1) := pow_nonneg hy _
  have hb : y^(n+1) / (1-y) ≤ 2*y^(n+1) := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hp (show 0 ≤ 1-2*y by linarith)]
  calc
    _ = |(∑ i ∈ Finset.range n, (-y)^(i+1) / ((i:ℝ)+1)) + Real.log (1+y)| := by rw [add_comm]
    _ ≤ _ := h.trans hb

#print axioms sinh_taylor25
#print axioms profile_taylor25
#print axioms normalized_profile_taylor25
#print axioms log_one_add_taylor
end Manuscript14.ParryAnalyticInputs
