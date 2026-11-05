import GegenbauerFock.Section8Section9

/-!
# V007 — quantitative bridge from finite-rank errors to Schatten powers

This module derives two genuine Lean summability statements for any
nonnegative sequence majorized by the *actual* Gegenbauer–Fock truncation
errors or by their certified factorial bounds.

The hypotheses are explicit. These lemmas DO NOT themselves assert that
an ordered list of the true singular values satisfies that majorization.
That additional approximation-number / singular-value comparison
(Eckart–Young in Hilbert spaces) remains to be kernel certified before
concluding Schatten membership of the actual operator for 0 < p < 2.
-/

noncomputable section

namespace GegenbauerFock.Section8Section9

/-- Every nonnegative sequence termwise dominated by the errors
`‖C - C_N‖` has summable real powers for all `p > 0`. -/
theorem summable_powers_below_actual_truncation_errors
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (sigma : ℕ → ℝ) (hsigma : ∀ N, 0 ≤ sigma N)
    (hmajor : ∀ N : ℕ,
      sigma N ≤ ‖Cf lam alpha hlam ha - CN lam alpha hlam ha N‖)
    (p : ℝ) (hp : 0 < p) :
    Summable (fun N : ℕ => (sigma N) ^ p) := by
  have hs :
      Summable (fun N : ℕ =>
        ‖Cf lam alpha hlam ha - CN lam alpha hlam ha N‖ ^ p) :=
    (theorem_8_1_schatten lam alpha hlam ha p hp).2
  apply Summable.of_nonneg_of_le
  · intro N
    exact Real.rpow_nonneg (hsigma N) p
  · intro N
    exact Real.rpow_le_rpow (hsigma N) (hmajor N) hp.le
  · exact hs

/-- The same all-p conclusion when the sequence is directly bounded
by the certified factorial majorant from Theorem 8.1. -/
theorem summable_powers_below_factorial_tails
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (sigma : ℕ → ℝ) (hsigma : ∀ N, 0 ≤ sigma N)
    (hmajor : ∀ N : ℕ, sigma N ≤ tailBound alpha N)
    (p : ℝ) (hp : 0 < p) :
    Summable (fun N : ℕ => (sigma N) ^ p) := by
  have hs :
      Summable (fun N : ℕ => (tailBound alpha N) ^ p) :=
    (theorem_8_1_schatten lam alpha hlam ha p hp).1
  apply Summable.of_nonneg_of_le
  · intro N
    exact Real.rpow_nonneg (hsigma N) p
  · intro N
    exact Real.rpow_le_rpow (hsigma N) (hmajor N) hp.le
  · exact hs

#print axioms GegenbauerFock.Section8Section9.summable_powers_below_actual_truncation_errors
#print axioms GegenbauerFock.Section8Section9.summable_powers_below_factorial_tails

end GegenbauerFock.Section8Section9
