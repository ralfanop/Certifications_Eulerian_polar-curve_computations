import EulerianGrothendieck.FirstOrderAsymptotics
import EulerianGrothendieck.ExactCoefficients

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- The falling factorial as a real polynomial, including values below its degree. -/
def fallingReal : ℕ → ℝ → ℝ
  | 0, _ => 1
  | q+1, x => fallingReal q x * (x-q)

theorem fallingReal_nat (q n : ℕ) : fallingReal q (n:ℝ) = (n.descFactorial q:ℝ) := by
  induction q with
  | zero => simp [fallingReal]
  | succ q ih =>
    rw [fallingReal, ih, Nat.descFactorial_succ]
    by_cases h : q ≤ n
    · rw [Nat.cast_mul, Nat.cast_sub h]
      ring
    · have hz : n.descFactorial q = 0 := Nat.descFactorial_of_lt (by omega)
      simp [hz]

theorem fallingReal_rat (q : ℕ) (x : ℚ) : fallingReal q (x:ℝ) = (fallingPoly q x:ℝ) := by
  induction q with
  | zero => simp [fallingReal, fallingPoly]
  | succ q ih => simp [fallingReal, fallingPoly, ih]

def exactMomentPolynomial (r : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (2*r+1), (pCoeff r q:ℝ)*2^q*fallingReal q x

def exactSquaredPolynomial (r : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (2*r+1), (qFallingCoeff r q:ℝ)*fallingReal q x

theorem exactMomentPolynomial_rat (r : ℕ) (x : ℚ) :
    exactMomentPolynomial r (x:ℝ) = (gPolynomial r x:ℝ) := by
  simp [exactMomentPolynomial, gPolynomial, fallingReal_rat]

theorem exactSquaredPolynomial_rat (r : ℕ) (x : ℚ) :
    exactSquaredPolynomial r (x:ℝ) = (qPolynomial r x:ℝ) := by
  simp [exactSquaredPolynomial, qPolynomial, fallingReal_rat]

theorem ratioRecurrenceCoefficient_eq_zero (n j : ℕ) (h : n < j) :
    ratioRecurrenceCoefficient n j = 0 := by
  simp [ratioRecurrenceCoefficient, Nat.descFactorial_of_lt h]

/-- Coefficient recurrence with a sum bounded by the asymptotic order, not the moment index. -/
theorem uniformRatio_coefficient_recurrence (n r : ℕ) :
    (uniformRatioPolynomial (n+1)).coeff r =
      ∑ j ∈ range (r+1), ratioRecurrenceCoefficient n j *
        (uniformRatioPolynomial (n-j)).coeff (r-j) := by
  rw [uniformRatioPolynomial_recurrence, Polynomial.finset_sum_coeff]
  simp only [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  let f := fun j => ratioRecurrenceCoefficient n j *
    (if j ≤ r then (uniformRatioPolynomial (n-j)).coeff (r-j) else 0)
  have he : (∑ j ∈ range (n+1), f j) = ∑ j ∈ range (r+1), f j := by
    by_cases h : n ≤ r
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hnot
      have hjn : n < j := by simp only [Finset.mem_range] at hnot; omega
      simp [f, ratioRecurrenceCoefficient_eq_zero n j hjn]
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hnot
      have hjr : ¬j ≤ r := by simp only [Finset.mem_range] at hnot; omega
      simp [f, hjr]
  change (∑ j ∈ range (n+1), f j) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  simp [f, show j ≤ r by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj]

theorem actual_cumulant_0 : standardUniformCumulant 0 = (1/2:ℝ) := by
  have h := standardUniformCumulant_recurrence 0
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial] at h
  linarith

theorem actual_cumulant_1 : standardUniformCumulant 1 = (-1/10:ℝ) := by
  have h := standardUniformCumulant_recurrence 1
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0] at h
  linarith

theorem actual_cumulant_2 : standardUniformCumulant 2 = (1/35:ℝ) := by
  have h := standardUniformCumulant_recurrence 2
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1] at h
  linarith

theorem actual_cumulant_3 : standardUniformCumulant 3 = (-3/350:ℝ) := by
  have h := standardUniformCumulant_recurrence 3
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2] at h
  linarith

theorem actual_cumulant_4 : standardUniformCumulant 4 = (1/385:ℝ) := by
  have h := standardUniformCumulant_recurrence 4
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3] at h
  linarith

theorem actual_cumulant_5 : standardUniformCumulant 5 = (-691/875875:ℝ) := by
  have h := standardUniformCumulant_recurrence 5
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4] at h
  linarith

theorem actual_cumulant_6 : standardUniformCumulant 6 = (6/25025:ℝ) := by
  have h := standardUniformCumulant_recurrence 6
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5] at h
  linarith

theorem actual_cumulant_7 : standardUniformCumulant 7 = (-10851/148898750:ℝ) := by
  have h := standardUniformCumulant_recurrence 7
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6] at h
  linarith

theorem actual_cumulant_8 : standardUniformCumulant 8 = (43867/1980353375:ℝ) := by
  have h := standardUniformCumulant_recurrence 8
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7] at h
  linarith

theorem actual_cumulant_9 : standardUniformCumulant 9 = (-523833/77799596875:ℝ) := by
  have h := standardUniformCumulant_recurrence 9
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8] at h
  linarith

theorem actual_cumulant_10 : standardUniformCumulant 10 = (466098/227740638125:ℝ) := by
  have h := standardUniformCumulant_recurrence 10
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8, actual_cumulant_9] at h
  linarith

theorem actual_cumulant_11 : standardUniformCumulant 11 = (-709092273/1139841893815625:ℝ) := by
  have h := standardUniformCumulant_recurrence 11
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8, actual_cumulant_9, actual_cumulant_10] at h
  linarith

theorem actual_cumulant_12 : standardUniformCumulant 12 = (11842758/62628675484375:ℝ) := by
  have h := standardUniformCumulant_recurrence 12
  norm_num [Finset.sum_range_succ, uniformEGFCoefficient, Nat.factorial, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8, actual_cumulant_9, actual_cumulant_10, actual_cumulant_11] at h
  linarith

theorem actual_cumulant_table (j : ℕ) (hj : j ≤ 12) :
    standardUniformCumulant j = (j+1:ℝ)*(cumulantA (j+1):ℝ) := by
  interval_cases j <;> norm_num [cumulantA, actual_cumulant_0, actual_cumulant_1, actual_cumulant_2, actual_cumulant_3, actual_cumulant_4, actual_cumulant_5, actual_cumulant_6, actual_cumulant_7, actual_cumulant_8, actual_cumulant_9, actual_cumulant_10, actual_cumulant_11, actual_cumulant_12]

end EulerianGrothendieck
