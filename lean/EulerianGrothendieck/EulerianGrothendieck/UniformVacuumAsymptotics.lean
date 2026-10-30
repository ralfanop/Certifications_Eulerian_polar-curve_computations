import EulerianGrothendieck.UniformKernel
import EulerianGrothendieck.ReciprocalAsymptotics

noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

theorem uniformRatio_eval_zero (k : ℕ) : (uniformRatioPolynomial k).eval 0 = 1 := by
  induction k with
  | zero => simp [uniformRatioPolynomial_zero]
  | succ k ih =>
    rw [uniformRatioPolynomial_recurrence, Polynomial.eval_finset_sum]
    rw [Finset.sum_eq_single 0]
    · simp [ratioRecurrenceCoefficient_zero, ih]
    · intro j hj hj0
      simp [hj0]
    · simp

theorem uniformSquaredPolynomial_constant (k : ℕ) : (uniformSquaredPolynomial k).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  rw [uniformSquaredPolynomial, Polynomial.eval_pow, uniformRatio_eval_zero, one_pow]

theorem binomialWeight_zero (t : ℝ) : binomialWeight t 0 = 1 := by
  norm_num [binomialWeight]

theorem binomialWeight_summable (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (binomialWeight t) := by
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg t) (show t^2 < 1 by nlinarith)).summable
  apply hg.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (binomialWeight_nonneg t k)]
  exact binomialWeight_le_geometric t k

theorem uniformNormCoefficient_zero (t : ℝ) :
    uniformNormCoefficient t 0 = ∑' k, binomialWeight t k := by
  simp [uniformNormCoefficient, uniformSquaredPolynomial_constant]

theorem uniformNormCoefficient_zero_ge_one (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    1 ≤ uniformNormCoefficient t 0 := by
  rw [uniformNormCoefficient_zero]
  have h := (binomialWeight_summable t ht0 ht1).le_tsum 0 (fun k hk => binomialWeight_nonneg t k)
  simpa only [binomialWeight_zero] using h

theorem uniformNormSeries_summable (M : ℕ) (hM : M ≠ 0) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (fun k => binomialWeight t k*(uniformMomentRatio M k)^2) := by
  apply (binomialWeight_summable t ht0 ht1).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (binomialWeight_nonneg t k)]
  apply mul_le_of_le_one_right (binomialWeight_nonneg t k)
  rw [← uniformSquaredPolynomial_value M k hM]
  exact uniformSquaredPolynomial_value_bound M k hM

theorem uniformNormSeries_ge_one (M : ℕ) (hM : M ≠ 0) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    1 ≤ uniformNormSeries M t := by
  have h := (uniformNormSeries_summable M hM t ht0 ht1).le_tsum 0
    (fun k hk => mul_nonneg (binomialWeight_nonneg t k) (sq_nonneg _))
  simpa only [binomialWeight_zero, uniformMomentRatio_exact_polynomial M 0 hM,
    uniformRatioPolynomial_zero, Polynomial.eval_one, one_pow, one_mul, uniformNormSeries] using h

def uniformVacuumCoefficient (t : ℝ) (r : ℕ) : ℝ :=
  inverseSeriesCoefficient (uniformNormCoefficient t) r

/-- Arbitrary finite-order expansion for the reciprocal of the exact uniform
norm series; its coefficient sequence is fixed independently of truncation order. -/
theorem uniformVacuumSeries_all_orders (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(uniformNormSeries M t)-∑ r ∈ range (R+1), uniformVacuumCoefficient t r/(M:ℝ)^r| ≤
        K/(M:ℝ)^(R+1) := by
  exact reciprocal_all_order_remainder (fun M => uniformNormSeries M t) (uniformNormCoefficient t)
    1 (by norm_num) (fun M hM => uniformNormSeries_ge_one M hM t ht0 ht1)
    (by have h := uniformNormCoefficient_zero_ge_one t ht0 ht1; linarith)
    (uniformNormSeries_all_orders t ht0 ht1) R

/-- The reciprocal theorem for the actual exponential product-law integral. -/
theorem uniform_vacuum_integral_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp (t*(standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := uniformVacuumSeries_all_orders t ht0 ht1 R
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [uniform_exponential_integral_eq_series U hU hind hlaw M hM t]
  exact hrem M hM

end EulerianGrothendieck
