import EulerianGrothendieck.CoefficientIdentification

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

theorem exactMomentPolynomial_recurrence_0 (x : ℝ) :
    exactMomentPolynomial 0 (x+1) =
      ∑ j ∈ range (0+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (0-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_1 (x : ℝ) :
    exactMomentPolynomial 1 (x+1) =
      ∑ j ∈ range (1+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (1-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_2 (x : ℝ) :
    exactMomentPolynomial 2 (x+1) =
      ∑ j ∈ range (2+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (2-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_3 (x : ℝ) :
    exactMomentPolynomial 3 (x+1) =
      ∑ j ∈ range (3+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (3-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_4 (x : ℝ) :
    exactMomentPolynomial 4 (x+1) =
      ∑ j ∈ range (4+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (4-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_5 (x : ℝ) :
    exactMomentPolynomial 5 (x+1) =
      ∑ j ∈ range (5+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (5-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_6 (x : ℝ) :
    exactMomentPolynomial 6 (x+1) =
      ∑ j ∈ range (6+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (6-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_7 (x : ℝ) :
    exactMomentPolynomial 7 (x+1) =
      ∑ j ∈ range (7+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (7-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_8 (x : ℝ) :
    exactMomentPolynomial 8 (x+1) =
      ∑ j ∈ range (8+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (8-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_9 (x : ℝ) :
    exactMomentPolynomial 9 (x+1) =
      ∑ j ∈ range (9+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (9-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_10 (x : ℝ) :
    exactMomentPolynomial 10 (x+1) =
      ∑ j ∈ range (10+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (10-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_11 (x : ℝ) :
    exactMomentPolynomial 11 (x+1) =
      ∑ j ∈ range (11+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (11-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence_12 (x : ℝ) :
    exactMomentPolynomial 12 (x+1) =
      ∑ j ∈ range (12+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (12-j) (x-j) := by
  norm_num [exactMomentPolynomial, pCoeff, cumulantA, fallingReal, Finset.sum_range_succ]
  <;> ring

theorem exactMomentPolynomial_recurrence (r : ℕ) (hr : r ≤ 12) (x : ℝ) :
    exactMomentPolynomial r (x+1) =
      ∑ j ∈ range (r+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (r-j) (x-j) := by
  interval_cases r
  · exact exactMomentPolynomial_recurrence_0 x
  · exact exactMomentPolynomial_recurrence_1 x
  · exact exactMomentPolynomial_recurrence_2 x
  · exact exactMomentPolynomial_recurrence_3 x
  · exact exactMomentPolynomial_recurrence_4 x
  · exact exactMomentPolynomial_recurrence_5 x
  · exact exactMomentPolynomial_recurrence_6 x
  · exact exactMomentPolynomial_recurrence_7 x
  · exact exactMomentPolynomial_recurrence_8 x
  · exact exactMomentPolynomial_recurrence_9 x
  · exact exactMomentPolynomial_recurrence_10 x
  · exact exactMomentPolynomial_recurrence_11 x
  · exact exactMomentPolynomial_recurrence_12 x

theorem exactMomentPolynomial_at_zero (r : ℕ) (hr : r ≤ 12) :
    exactMomentPolynomial r 0 = if r=0 then 1 else 0 := by
  interval_cases r <;> norm_num [exactMomentPolynomial, pCoeff, fallingReal, Finset.sum_range_succ]

/-- All moment indices, with the first thirteen coefficients identified explicitly. -/
theorem actual_moment_coefficients_through_twelve (k r : ℕ) (hr : r ≤ 12) :
    (uniformRatioPolynomial k).coeff r = exactMomentPolynomial r k := by
  induction k using Nat.strong_induction_on generalizing r with
  | h k ih =>
    cases k with
    | zero =>
      rw [uniformRatioPolynomial_zero, Polynomial.coeff_one, Nat.cast_zero,
        exactMomentPolynomial_at_zero r hr]
    | succ n =>
      rw [uniformRatio_coefficient_recurrence, Nat.cast_add, Nat.cast_one,
        exactMomentPolynomial_recurrence r hr]
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hjn : j ≤ n
      · rw [ih (n-j) (by omega) (r-j) (by omega), ratioRecurrenceCoefficient,
          actual_cumulant_table j (by omega), fallingReal_nat, Nat.cast_sub hjn]
      · rw [ratioRecurrenceCoefficient_eq_zero n j (by omega), fallingReal_nat,
          Nat.descFactorial_of_lt (by omega)]
        simp

end EulerianGrothendieck
