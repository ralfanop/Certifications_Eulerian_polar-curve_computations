import Mathlib

/-!
# V007: factorially summable Fock coherent coefficient energies

For every α>0 the nonnegative real weights c^n/n!,
c=1/(4α), form a summable family, with the Gaussian coherent-state
scalar parameter. These are the majorants for the squared norms of
the *actual* Gegenbauer-Fock monomial Riesz coefficients, once those
coefficients are linked to their L² moment vectors.

No separate custom axiom, numerical approximation or sorry.
-/

namespace GegenbauerFock.FactorialEnergy

/-- Positive Gaussian parameter for the Fock coefficient norm series. -/
noncomputable def c (alpha : ℝ) : ℝ := 1 / (4 * alpha)

/-- The exact scalar n-th squared coefficient weight. -/
noncomputable def weightSq (alpha : ℝ) (n : ℕ) : ℝ :=
  (c alpha) ^ n / (Nat.factorial n : ℝ)

/-- Fock scalar majorants are summable for arbitrary real positive alpha. -/
theorem weightSq_summable (alpha : ℝ) :
    Summable (weightSq alpha) := by
  exact Real.summable_pow_div_factorial (c alpha)

/-- The weights are nonnegative for alpha>0. -/
theorem weightSq_nonneg (alpha : ℝ) (hα : 0 < alpha) (n : ℕ) :
    0 ≤ weightSq alpha n := by
  unfold weightSq c
  positivity

/-- The positive square-root amplitude used for Riesz coefficients. -/
noncomputable def weight (alpha : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (weightSq alpha n)

/-- Exact relation between the scalar amplitudes and squared energies. -/
theorem weight_sq (alpha : ℝ) (hα : 0 < alpha) (n : ℕ) :
    weight alpha n ^ 2 = weightSq alpha n := by
  unfold weight
  exact Real.sq_sqrt (weightSq_nonneg alpha hα n)

/-- The scalar coefficients are square-summable, without restricting α. -/
theorem weight_square_summable (alpha : ℝ) (hα : 0 < alpha) :
    Summable (fun n : ℕ => weight alpha n ^ 2) := by
  simpa only [weight_sq alpha hα] using (weightSq_summable alpha)

#print axioms GegenbauerFock.FactorialEnergy.weightSq_summable
#print axioms GegenbauerFock.FactorialEnergy.weightSq_nonneg
#print axioms GegenbauerFock.FactorialEnergy.weight_sq
#print axioms GegenbauerFock.FactorialEnergy.weight_square_summable

end GegenbauerFock.FactorialEnergy
