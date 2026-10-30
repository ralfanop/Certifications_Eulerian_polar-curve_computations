import EulerianGrothendieck.CentralBinomialSeries

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck

theorem uniformRatioPolynomial_one : uniformRatioPolynomial 1 = 1 := by
  rw [show 1=0+1 by rfl, uniformRatioPolynomial_recurrence]
  simp [ratioRecurrenceCoefficient_zero, uniformRatioPolynomial_zero]

theorem uniformRatio_linear_recurrence (r : ℕ) :
    (uniformRatioPolynomial (r+2)).coeff 1 =
      (uniformRatioPolynomial (r+1)).coeff 1 - 2*(r+1:ℝ)/5 := by
  rw [uniformRatioPolynomial_recurrence, Polynomial.finset_sum_coeff]
  have hs := Finset.sum_subset (s₁ := ({0,1}:Finset ℕ)) (s₂ := range (r+1+1))
    (f := fun j => (C (ratioRecurrenceCoefficient (r+1) j)*X^j*
      uniformRatioPolynomial (r+1-j)).coeff 1)
    (by intro j hj; simp only [mem_insert, mem_singleton] at hj; rcases hj with rfl|rfl <;> simp)
    (by
      intro j hj hnot
      dsimp only
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      have hj2 : ¬ j ≤ 1 := by simp only [mem_insert, mem_singleton, not_or] at hnot; omega
      simp [hj2])
  rw [← hs]
  simp only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true,
    sum_singleton, Nat.sub_zero, Nat.add_sub_cancel, pow_zero, mul_one,
    pow_one, mul_assoc, coeff_C_mul, coeff_X_mul, ratioRecurrenceCoefficient_zero]
  rw [Polynomial.coeff_zero_eq_eval_zero, uniformRatio_eval_zero]
  simp [ratioRecurrenceCoefficient, standardUniformCumulant_one, Nat.descFactorial_succ]
  ring

theorem uniformRatio_first_coefficient (k : ℕ) :
    (uniformRatioPolynomial k).coeff 1 = -(k:ℝ)*(k-1)/5 := by
  induction k with
  | zero => simp [uniformRatioPolynomial_zero, Polynomial.coeff_one]
  | succ k ih =>
    cases k with
    | zero => simp [uniformRatioPolynomial_one, Polynomial.coeff_one]
    | succ k =>
      rw [uniformRatio_linear_recurrence, ih]
      push_cast
      ring

theorem uniformSquaredPolynomial_first_coefficient (k : ℕ) :
    (uniformSquaredPolynomial k).coeff 1 = -2*(k:ℝ)*(k-1)/5 := by
  rw [uniformSquaredPolynomial, pow_two, Polynomial.mul_coeff_one]
  simp only [uniformRatio_first_coefficient, Polynomial.coeff_zero_eq_eval_zero, uniformRatio_eval_zero]
  ring

end EulerianGrothendieck
