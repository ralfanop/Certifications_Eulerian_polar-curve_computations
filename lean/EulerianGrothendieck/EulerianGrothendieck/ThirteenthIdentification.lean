import EulerianGrothendieck.ThirteenthMomentRecurrence
import EulerianGrothendieck.ThirteenthSquaredPolynomial
import EulerianGrothendieck.ThirteenthRationalCertificates
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck.Order13
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
theorem actual_cumulant_13 : standardUniformCumulant 13 = (-6785560294/118055053288046875:ℝ) := by
  have h := standardUniformCumulant_recurrence 13
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial,
    actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8, actual_cumulant_9, actual_cumulant_10, actual_cumulant_11, actual_cumulant_12] at h
  linarith

theorem actual_cumulant_table (j : ℕ) (hj : j ≤ 13) :
    standardUniformCumulant j = (j+1:ℝ)*(cumulantA (j+1):ℝ) := by
  by_cases h : j ≤ 12
  · rw [cumulantA_prefix (j+1) (by omega)]
    exact EulerianGrothendieck.actual_cumulant_table j h
  · have he : j = 13 := by omega
    subst j
    norm_num [cumulantA, actual_cumulant_13]

theorem exactMomentPolynomial_recurrence (r : ℕ) (hr : r ≤ 13) (x : ℝ) :
    exactMomentPolynomial r (x+1) =
      ∑ j ∈ range (r+1), 2^(j+1)*fallingReal j x*((j+1:ℝ)*(cumulantA (j+1):ℝ))*
        exactMomentPolynomial (r-j) (x-j) := by
  by_cases h : r ≤ 12
  · rw [exactMomentPolynomial_prefix r h,
      EulerianGrothendieck.exactMomentPolynomial_recurrence r h]
    apply Finset.sum_congr rfl
    intro j hj
    have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [cumulantA_prefix (j+1) (by omega), exactMomentPolynomial_prefix (r-j) (by omega)]
  · have he : r = 13 := by omega
    subst r
    exact exactMomentPolynomial_recurrence_13 x

theorem exactMomentPolynomial_at_zero (r : ℕ) (hr : r ≤ 13) :
    exactMomentPolynomial r 0 = if r=0 then 1 else 0 := by
  by_cases h : r ≤ 12
  · rw [exactMomentPolynomial_prefix r h]
    exact EulerianGrothendieck.exactMomentPolynomial_at_zero r h
  · have he : r = 13 := by omega
    subst r
    norm_num [exactMomentPolynomial, pCoeff, fallingReal, Finset.sum_range_succ]

/-- Actual coefficients, for every moment index k, including the new order 13. -/
theorem actual_moment_coefficients_through_thirteen (k r : ℕ) (hr : r ≤ 13) :
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

theorem exact_squared_polynomial_table (r : ℕ) (hr : r ≤ 13) (x : ℚ) :
    (∑ j ∈ range (r+1), gPolynomial j x*gPolynomial (r-j) x) = qPolynomial r x := by
  by_cases h : r ≤ 12
  · rw [qPolynomial_prefix r h]
    calc
      _ = ∑ j ∈ range (r+1), EulerianGrothendieck.gPolynomial j x *
          EulerianGrothendieck.gPolynomial (r-j) x := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [gPolynomial_prefix j (by omega), gPolynomial_prefix (r-j) (by omega)]
      _ = _ := EulerianGrothendieck.exact_squared_polynomial_table r h x
  · have he : r = 13 := by omega
    subst r
    exact squared_moment_polynomial_13 x

theorem actual_squared_coefficients_through_thirteen (k r : ℕ) (hr : r ≤ 13) :
    (uniformSquaredPolynomial k).coeff r = exactSquaredPolynomial r k := by
  rw [uniformSquaredPolynomial, pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j l => (uniformRatioPolynomial k).coeff j*(uniformRatioPolynomial k).coeff l) r]
  calc
    _ = ∑ j ∈ range (r+1), exactMomentPolynomial j k*exactMomentPolynomial (r-j) k := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [actual_moment_coefficients_through_thirteen k j (by omega),
        actual_moment_coefficients_through_thirteen k (r-j) (by omega)]
    _ = exactSquaredPolynomial r k := by
      have h := congrArg (fun x : ℚ => (x:ℝ)) (exact_squared_polynomial_table r hr (k:ℚ))
      simpa only [Rat.cast_sum, Rat.cast_mul, ← exactMomentPolynomial_rat,
        ← exactSquaredPolynomial_rat, Rat.cast_natCast] using h

theorem norm_coefficient_table (r : ℕ) (hr : r ≤ 13) :
    normB r = ∑ q ∈ range (2*r+1), qFallingCoeff r q*nbFactorial q := by
  by_cases h : r ≤ 12
  · simp only [normB_prefix r h, qFallingCoeff_prefix r _ h]
    exact EulerianGrothendieck.norm_coefficient_table r h
  · have he : r = 13 := by omega
    subst r
    exact norm_coefficient_13

theorem reciprocal_coefficient_table (r : ℕ) (hr : r ≤ 13) :
    (∑ j ∈ range (r+1), normB j*vacuumD (r-j)) = if r=0 then 1 else 0 := by
  by_cases h : r ≤ 12
  · calc
      _ = ∑ j ∈ range (r+1), EulerianGrothendieck.normB j *
          EulerianGrothendieck.vacuumD (r-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [normB_prefix j (by omega), vacuumD_prefix (r-j) (by omega)]
      _ = _ := EulerianGrothendieck.reciprocal_coefficient_table r h
  · have he : r = 13 := by omega
    subst r
    exact reciprocal_coefficient_13

theorem arithmetic_norm_coefficient_identification (r : ℕ) (hr : r ≤ 13) :
    uniformNormCoefficient arithmeticParameter r =
      (1/Real.sqrt (4/5))*(normB r:ℝ) := by
  unfold uniformNormCoefficient
  simp_rw [actual_squared_coefficients_through_thirteen _ r hr, arithmetic_weight_identity,
    exactSquaredPolynomial, Finset.mul_sum]
  have hterm : ∀ k q : ℕ,
      (centralCoefficient k*(1/5:ℝ)^k)*((qFallingCoeff r q:ℝ)*fallingReal q k) =
        (qFallingCoeff r q:ℝ)*(fallingReal q k*centralCoefficient k*(1/5:ℝ)^k) := by
    intros; ring
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun q hq =>
    (centralFactorialMoment_summable (1/5) (by norm_num) (by norm_num) q).mul_left (qFallingCoeff r q:ℝ))]
  simp_rw [tsum_mul_left]
  change (∑ q ∈ range (2*r+1), (qFallingCoeff r q:ℝ)*centralFactorialMoment (1/5) q) = _
  simp_rw [centralFactorialMoment_one_fifth]
  rw [norm_coefficient_table r hr]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring


theorem arithmetic_vacuum_coefficient_identification (r : ℕ) (hr : r ≤ 13) :
    uniformVacuumCoefficient arithmeticParameter r = Real.sqrt (4/5)*(vacuumD r:ℝ) := by
  have hs : 0 < Real.sqrt (4/5:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply inverseSeriesCoefficient_prefix_unique (uniformNormCoefficient arithmeticParameter)
    (fun j => Real.sqrt (4/5)*(vacuumD j:ℝ))
    (by have h := uniformNormCoefficient_zero_ge_one arithmeticParameter
          arithmeticParameter_properties.1 arithmeticParameter_properties.2.1; linarith) 13 ?_ r hr
  intro n hn
  have he : (∑ j ∈ range (n+1), uniformNormCoefficient arithmeticParameter j*
      (Real.sqrt (4/5)*(vacuumD (n-j):ℝ))) =
      ((∑ j ∈ range (n+1), normB j*vacuumD (n-j):ℚ):ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [arithmetic_norm_coefficient_identification j (by have := Finset.mem_range.mp hj; omega)]
    field_simp
  rw [he, reciprocal_coefficient_table n hn]
  split_ifs <;> norm_num


end EulerianGrothendieck.Order13
