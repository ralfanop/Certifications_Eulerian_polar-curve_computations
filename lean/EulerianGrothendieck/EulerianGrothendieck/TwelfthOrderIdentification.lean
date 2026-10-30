import EulerianGrothendieck.MomentPolynomialBridge
import EulerianGrothendieck.CentralFactorialMoments
import EulerianGrothendieck.RawScaleAsymptotics

noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem exact_squared_polynomial_table (r : ℕ) (hr : r ≤ 12) (x : ℚ) :
    (∑ j ∈ range (r+1), gPolynomial j x*gPolynomial (r-j) x) = qPolynomial r x := by
  interval_cases r
  · norm_num [gPolynomial, pCoeff, qPolynomial, qFallingCoeff, fallingPoly]
  · exact squared_moment_polynomial_1 x
  · exact squared_moment_polynomial_2 x
  · exact squared_moment_polynomial_3 x
  · exact squared_moment_polynomial_4 x
  · exact squared_moment_polynomial_5 x
  · exact squared_moment_polynomial_6 x
  · exact squared_moment_polynomial_7 x
  · exact squared_moment_polynomial_8 x
  · exact squared_moment_polynomial_9 x
  · exact squared_moment_polynomial_10 x
  · exact squared_moment_polynomial_11 x
  · exact squared_moment_polynomial_12 x

theorem actual_squared_coefficients_through_twelve (k r : ℕ) (hr : r ≤ 12) :
    (uniformSquaredPolynomial k).coeff r = exactSquaredPolynomial r k := by
  rw [uniformSquaredPolynomial, pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j l => (uniformRatioPolynomial k).coeff j*(uniformRatioPolynomial k).coeff l) r]
  calc
    _ = ∑ j ∈ range (r+1), exactMomentPolynomial j k*exactMomentPolynomial (r-j) k := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [actual_moment_coefficients_through_twelve k j (by omega),
        actual_moment_coefficients_through_twelve k (r-j) (by omega)]
    _ = exactSquaredPolynomial r k := by
      have h := congrArg (fun x : ℚ => (x:ℝ)) (exact_squared_polynomial_table r hr (k:ℚ))
      simpa only [Rat.cast_sum, Rat.cast_mul, ← exactMomentPolynomial_rat,
        ← exactSquaredPolynomial_rat, Rat.cast_natCast] using h

theorem norm_coefficient_table (r : ℕ) (hr : r ≤ 12) :
    normB r = ∑ q ∈ range (2*r+1), qFallingCoeff r q*nbFactorial q := by
  interval_cases r
  · norm_num [normB, qFallingCoeff, nbFactorial]
  · exact norm_coefficient_1
  · exact norm_coefficient_2
  · exact norm_coefficient_3
  · exact norm_coefficient_4
  · exact norm_coefficient_5
  · exact norm_coefficient_6
  · exact norm_coefficient_7
  · exact norm_coefficient_8
  · exact norm_coefficient_9
  · exact norm_coefficient_10
  · exact norm_coefficient_11
  · exact norm_coefficient_12

def arithmeticParameter : ℝ := 1/Real.sqrt 5

theorem arithmeticParameter_properties :
    0 < arithmeticParameter ∧ arithmeticParameter < 1 ∧ arithmeticParameter^2 = 1/5 := by
  have hs : 0 < Real.sqrt (5:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt (5:ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  refine ⟨by unfold arithmeticParameter; positivity, ?_, ?_⟩
  · unfold arithmeticParameter
    apply (div_lt_one hs).2
    nlinarith
  · unfold arithmeticParameter
    rw [div_pow, hsq]
    norm_num

theorem arithmetic_weight_identity (k : ℕ) :
    binomialWeight arithmeticParameter k = centralCoefficient k*(1/5:ℝ)^k := by
  simp only [binomialWeight, centralCoefficient, Nat.centralBinom, pow_mul,
    arithmeticParameter_properties.2.2]

theorem arithmetic_norm_coefficient_identification (r : ℕ) (hr : r ≤ 12) :
    uniformNormCoefficient arithmeticParameter r =
      (1/Real.sqrt (4/5))*(normB r:ℝ) := by
  unfold uniformNormCoefficient
  simp_rw [actual_squared_coefficients_through_twelve _ r hr, arithmetic_weight_identity,
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

theorem reciprocal_coefficient_table (r : ℕ) (hr : r ≤ 12) :
    (∑ j ∈ range (r+1), normB j*vacuumD (r-j)) = if r=0 then 1 else 0 := by
  interval_cases r
  · norm_num [normB, vacuumD]
  · exact reciprocal_coefficient_1
  · exact reciprocal_coefficient_2
  · exact reciprocal_coefficient_3
  · exact reciprocal_coefficient_4
  · exact reciprocal_coefficient_5
  · exact reciprocal_coefficient_6
  · exact reciprocal_coefficient_7
  · exact reciprocal_coefficient_8
  · exact reciprocal_coefficient_9
  · exact reciprocal_coefficient_10
  · exact reciprocal_coefficient_11
  · exact reciprocal_coefficient_12

theorem inverseSeriesCoefficient_convolution (b : ℕ → ℝ) (hb : b 0 ≠ 0) (r : ℕ) :
    (∑ j ∈ range (r+1), b j*inverseSeriesCoefficient b (r-j)) = if r=0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) r)
    (PowerSeries.mul_inv_cancel (PowerSeries.mk b) (by simpa using hb))
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j l => PowerSeries.coeff j (PowerSeries.mk b)*
      PowerSeries.coeff l ((PowerSeries.mk b)⁻¹)) r,
    PowerSeries.coeff_one] at h
  simpa only [PowerSeries.coeff_mk, inverseSeriesCoefficient] using h

theorem inverseSeriesCoefficient_prefix_unique (b d : ℕ → ℝ) (hb : b 0 ≠ 0) (R : ℕ)
    (hconv : ∀ r ≤ R, (∑ j ∈ range (r+1), b j*d (r-j)) = if r=0 then 1 else 0)
    (r : ℕ) (hr : r ≤ R) : inverseSeriesCoefficient b r = d r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have h1 := inverseSeriesCoefficient_convolution b hb r
    have h2 := hconv r hr
    rw [Finset.sum_range_succ'] at h1 h2
    simp only [Nat.sub_zero] at h1 h2
    have ht : (∑ j ∈ range r, b (j+1)*inverseSeriesCoefficient b (r-(j+1))) =
        ∑ j ∈ range r, b (j+1)*d (r-(j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j < r := Finset.mem_range.mp hj
      rw [ih (r-(j+1)) (by omega) (by omega)]
    rw [ht] at h1
    apply mul_left_cancel₀ hb
    linarith

theorem arithmetic_vacuum_coefficient_identification (r : ℕ) (hr : r ≤ 12) :
    uniformVacuumCoefficient arithmeticParameter r = Real.sqrt (4/5)*(vacuumD r:ℝ) := by
  have hs : 0 < Real.sqrt (4/5:ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply inverseSeriesCoefficient_prefix_unique (uniformNormCoefficient arithmeticParameter)
    (fun j => Real.sqrt (4/5)*(vacuumD j:ℝ))
    (by have h := uniformNormCoefficient_zero_ge_one arithmeticParameter
          arithmeticParameter_properties.1 arithmeticParameter_properties.2.1; linarith) 12 ?_ r hr
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

end EulerianGrothendieck
