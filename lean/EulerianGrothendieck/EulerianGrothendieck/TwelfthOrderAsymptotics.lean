import EulerianGrothendieck.TwelfthOrderIdentification

noncomputable section
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

/-- All twelve explicitly tabulated fractions are coefficients of the actual
uniform exponential integral, with an independently proved M^-13 remainder. -/
theorem actual_uniform_vacuum_twelfth_order
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp (arithmeticParameter*
        (standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) -
        Real.sqrt (4/5)*(∑ r ∈ range 13, (vacuumD r:ℝ)/(M:ℝ)^r)| ≤ K/(M:ℝ)^13 := by
  obtain ⟨K,hK,hrem⟩ := uniform_vacuum_integral_all_orders U hU hind hlaw arithmeticParameter
    arithmeticParameter_properties.1 arithmeticParameter_properties.2.1 12
  refine ⟨K,hK,?_⟩
  intro M hM
  have h := hrem M hM
  have he : (∑ r ∈ range 13, uniformVacuumCoefficient arithmeticParameter r/(M:ℝ)^r) =
      Real.sqrt (4/5)*(∑ r ∈ range 13, (vacuumD r:ℝ)/(M:ℝ)^r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [arithmetic_vacuum_coefficient_identification r (by have := Finset.mem_range.mp hr; omega)]
    ring
  simpa only [show (12:ℕ)+1=13 by rfl, he] using h

/-- The D12 expansion in the original, unstandardized scale alpha=(sqrt 5/12) M. -/
theorem arithmetic_scale_vacuum_twelfth_order
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M →
      |(1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/
        ((Real.sqrt 5/12)*(M:ℝ))) ∂μ.prod μ))/Real.sqrt (4/5) -
        (∑ r ∈ range 13, (vacuumD r:ℝ)/(M:ℝ)^r)| ≤ K/(M:ℝ)^13 := by
  obtain ⟨K,hK,hrem⟩ := actual_uniform_vacuum_twelfth_order U hU hind hlaw
  have hs : 0 < Real.sqrt (4/5:ℝ) := Real.sqrt_pos.2 (by norm_num)
  refine ⟨K/Real.sqrt (4/5)+1, by positivity, ?_⟩
  intro M hM
  have hm : M ≠ 0 := by omega
  have he : (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/
      ((Real.sqrt 5/12)*(M:ℝ))) ∂μ.prod μ) =
      ∫ xy, Real.exp (arithmeticParameter*
        (standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ := by
    rw [raw_uniform_kernel_identity U hU hind hlaw (Real.sqrt 5/12) (by positivity) M hm,
      uniform_exponential_integral_eq_series U hU hind hlaw M hm arithmeticParameter]
    congr 1
    unfold arithmeticParameter
    ring
  rw [he]
  have h := div_le_div_of_nonneg_right (hrem M hm) hs.le
  rw [← abs_of_pos hs, ← abs_div, sub_div] at h
  have hc : Real.sqrt (4/5)*(∑ r ∈ range 13, (vacuumD r:ℝ)/(M:ℝ)^r)/Real.sqrt (4/5) =
      ∑ r ∈ range 13, (vacuumD r:ℝ)/(M:ℝ)^r := by field_simp
  rw [abs_of_pos hs, hc] at h
  calc
    _ ≤ (K/(M:ℝ)^13)/Real.sqrt (4/5) := h
    _ = (K/Real.sqrt (4/5))/(M:ℝ)^13 := div_right_comm _ _ _
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end EulerianGrothendieck
