import EulerianGrothendieck.FirstOrderAsymptotics

noncomputable section
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

theorem normalized_scale_mem (c : ℝ) (hc : 1/12 < c) :
    0 < 1/(12*c) ∧ 1/(12*c) < 1 := by
  have hc0 : 0 < c := by linarith
  exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

theorem standardized_exponent_identity (c a b : ℝ) (hc : c ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    (1/(12*c))*((Real.sqrt (12/(M:ℝ))*a)*(Real.sqrt (12/(M:ℝ))*b)) = a*b/(c*(M:ℝ)) := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  calc
    _ = (1/(12*c))*(Real.sqrt (12/(M:ℝ)))^2*a*b := by ring
    _ = a*b/(c*(M:ℝ)) := by rw [Real.sq_sqrt (by positivity)]; field_simp

theorem raw_uniform_kernel_identity
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : c ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/(c*(M:ℝ))) ∂μ.prod μ) =
      uniformNormSeries M (1/(12*c)) := by
  rw [← uniform_exponential_integral_eq_series U hU hind hlaw M hM (1/(12*c))]
  apply integral_congr_ae
  filter_upwards with xy
  rw [standardizedUniformSum, standardizedUniformSum, standardized_exponent_identity c _ _ hc M hM]

theorem raw_uniform_kernel_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/(c*(M:ℝ))) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformNormCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  have ht := normalized_scale_mem c hc
  obtain ⟨K, hK, hrem⟩ := uniformNormSeries_all_orders (1/(12*c)) ht.1 ht.2 R
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [raw_uniform_kernel_identity U hU hind hlaw c (by linarith) M hM]
  exact hrem M hM

theorem raw_uniform_vacuum_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/(c*(M:ℝ))) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  have ht := normalized_scale_mem c hc
  obtain ⟨K, hK, hrem⟩ := uniformVacuumSeries_all_orders (1/(12*c)) ht.1 ht.2 R
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [raw_uniform_kernel_identity U hU hind hlaw c (by linarith) M hM]
  exact hrem M hM

theorem raw_uniform_vacuum_first_order
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) :
    let t := 1/(12*c)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/(c*(M:ℝ))) ∂μ.prod μ) -
        Real.sqrt (1-t^2)*(1+(3*t^4/(10*(1-t^2)^2))/(M:ℝ))| ≤ K/(M:ℝ)^2 := by
  dsimp only
  have ht := normalized_scale_mem c hc
  obtain ⟨K, hK, hrem⟩ := uniformVacuum_first_order (1/(12*c)) ht.1 ht.2
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [raw_uniform_kernel_identity U hU hind hlaw c (by linarith) M hM]
  exact hrem M hM

end EulerianGrothendieck
