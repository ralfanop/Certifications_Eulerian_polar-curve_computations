import EulerianGrothendieck.ExponentialKernel

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Finset Filter
namespace EulerianGrothendieck

def standardizedUniformSum {Ω : Type*} (U : ℕ → Ω → ℝ) (M : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (12/(M:ℝ))*(∑ i ∈ range M, U i ω)

theorem uniform_sequence_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) :
    ∀ᵐ ω ∂μ, ∀ i : ℕ, |U i ω| ≤ 1/2 := by
  apply ae_all_iff.2
  intro i
  apply ae_of_ae_map (μ := μ) (p := fun x : ℝ => |x| ≤ 1/2) (hU i).aemeasurable
  rw [hlaw i, V033.UniformSum.uniformLaw]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩

theorem uniform_sum_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) :
    ∀ᵐ ω ∂μ, |∑ i ∈ range M, U i ω| ≤ (M:ℝ)/2 := by
  filter_upwards [uniform_sequence_ae_bound U hU hlaw] with ω hω
  calc
    _ ≤ ∑ i ∈ range M, |U i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range M, (1/2:ℝ) := Finset.sum_le_sum (fun i hi => hω i)
    _ = (M:ℝ)/2 := by simp; ring

theorem standardizedUniformSum_measurable
    {Ω : Type*} [MeasurableSpace Ω] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (M : ℕ) : Measurable (standardizedUniformSum U M) := by
  exact (Finset.measurable_fun_sum (range M) (fun i hi => hU i)).const_mul _

theorem standardizedUniformSum_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) :
    ∀ᵐ ω ∂μ, |standardizedUniformSum U M ω| ≤ Real.sqrt (12/(M:ℝ))*((M:ℝ)/2) := by
  filter_upwards [uniform_sum_ae_bound U hU hlaw M] with ω hω
  rw [standardizedUniformSum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)

theorem standardizedUniformSum_odd_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M k : ℕ) :
    (∫ ω, (standardizedUniformSum U M ω)^(2*k+1) ∂μ) = 0 := by
  simp only [standardizedUniformSum, mul_pow]
  rw [integral_const_mul, (V033.UniformSum.all_sum_moments U hU hind hlaw M _).2,
    V033.UniformSum.sumMoment_odd, mul_zero]

theorem binomialWeight_moment_identity (t m : ℝ) (k : ℕ) :
    (t^(2*k)/((2*k).factorial:ℝ))*m^2 =
      binomialWeight t k * (m/(((2*k).factorial:ℝ)/(2^k*(k.factorial:ℝ))))^2 := by
  unfold binomialWeight
  rw [Nat.cast_choose ℝ (show k ≤ 2*k by omega), show 2*k-k=k by omega]
  have hp : (4:ℝ)^k = (2^k)^2 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  rw [hp]
  field_simp
  <;> ring

/-- Exact identification, for every M>=1 and every real t. -/
theorem uniform_exponential_integral_eq_series
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) (hM : M ≠ 0)
    (t : ℝ) :
    (∫ xy, Real.exp (t*(standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) =
      uniformNormSeries M t := by
  rw [bounded_product_exp_even_series (standardizedUniformSum U M)
    (standardizedUniformSum_measurable U hU M) (Real.sqrt (12/(M:ℝ))*((M:ℝ)/2)) t
    (by positivity) (standardizedUniformSum_ae_bound U hU hlaw M)
    (standardizedUniformSum_odd_moment U hU hind hlaw M)]
  unfold uniformNormSeries
  apply tsum_congr
  intro k
  rw [binomialWeight_moment_identity]
  rw [show (∫ ω, (standardizedUniformSum U M ω)^(2*k) ∂μ) /
      (((2*k).factorial:ℝ)/(2^k*(k.factorial:ℝ))) = uniformMomentRatio M k from
    actual_uniform_sum_moment_ratio U hU hind hlaw M k hM]

/-- Complete probability-integral asymptotic, at every fixed finite order.
The only probabilistic hypotheses are measurability, independence, and the
uniform law. The remainder constant is independent of the number of summands. -/
theorem uniform_exponential_integral_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |(∫ xy, Real.exp (t*(standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformNormCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := uniformNormSeries_all_orders t ht0 ht1 R
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [uniform_exponential_integral_eq_series U hU hind hlaw M hM t]
  exact hrem M hM

end EulerianGrothendieck
