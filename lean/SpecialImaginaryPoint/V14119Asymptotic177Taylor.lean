import Mathlib

/-!
# Manuscript 14.119 — equation (177): rigorous hyperbolic Taylor input

The asymptotic formula for the Parry index requires a uniform estimate
for epsilon(x)=(sinh(x)-x)/x near x=0.

This module proves the first analytic remainder bound, using Mathlib's
quantitative Real.exp_bound on positive and negative arguments.

It intentionally does NOT assert the final logarithmic big-O estimate:
that needs additional logarithm/reciprocal estimates and remains open.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

/-- On 0 ≤ x ≤ 1, a uniform Taylor bound for real sinh through degree five.
In particular the remainder is quantified, not only an unbounded O. -/
theorem sinh_taylor5_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)| ≤ x ^ 7 / 4410 := by
  let P : ℝ := ∑ m ∈ Finset.range 7, x ^ m / (m.factorial : ℝ)
  let M : ℝ := ∑ m ∈ Finset.range 7, (-x) ^ m / (m.factorial : ℝ)
  let E : ℝ := |x| ^ 7 * (8 : ℝ) *
      ((((Nat.factorial 7 : ℕ) : ℝ) * 7)⁻¹)
  have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hmabs : |-x| ≤ 1 := by simpa only [abs_neg] using hxabs
  have hplus : |Real.exp x - P| ≤ E := by
    have h := Real.exp_bound (x := x) hxabs (n := 7) (by norm_num)
    simpa [P, E, div_eq_mul_inv, mul_assoc] using h
  have hminus : |Real.exp (-x) - M| ≤ E := by
    have h := Real.exp_bound (x := -x) hmabs (n := 7) (by norm_num)
    simpa [M, E, abs_neg, div_eq_mul_inv, mul_assoc] using h
  have hdiff :
      |(Real.exp x - Real.exp (-x)) - (P - M)| ≤ 2 * E := by
    rcases abs_le.mp hplus with ⟨hl1, hu1⟩
    rcases abs_le.mp hminus with ⟨hl2, hu2⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hfinite : (P - M) / 2 = x + x ^ 3 / 6 + x ^ 5 / 120 := by
    dsimp [P, M]
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  have hsinh :
      Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120) =
        ((Real.exp x - Real.exp (-x)) - (P - M)) / 2 := by
    rw [Real.sinh_eq, ← hfinite]
    ring
  have heqE : E = x ^ 7 / 4410 := by
    dsimp [E]
    rw [abs_of_nonneg hx0]
    norm_num [Nat.factorial] <;> ring
  rw [hsinh]
  calc
    |((Real.exp x - Real.exp (-x)) - (P - M)) / 2| =
        |(Real.exp x - Real.exp (-x)) - (P - M)| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 * E) / 2 := div_le_div_of_nonneg_right hdiff (by norm_num)
    _ = x ^ 7 / 4410 := by rw [heqE]; ring

/-- Uniform expansion for epsilon=(sinh(x)-x)/x, valid at every 0<x≤1.
This is the analytic input needed for the quotient in (177). -/
theorem epsilon_taylor_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |(Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120| ≤
      x ^ 6 / 4410 := by
  have h := sinh_taylor5_bound x hx0.le hx1
  have hxne : x ≠ 0 := ne_of_gt hx0
  have heq :
      (Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120 =
        (Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)) / x := by
    field_simp [hxne]
    ring
  rw [heq, abs_div, abs_of_pos hx0]
  have hdiv := div_le_div_of_nonneg_right h hx0.le
  calc
    |Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)| / x ≤
        (x ^ 7 / 4410) / x := hdiv
    _ = x ^ 6 / 4410 := by
      field_simp [hxne] <;> ring

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.sinh_taylor5_bound
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.epsilon_taylor_bound

end SpecialImaginaryPoint.V14119Asymptotic177
