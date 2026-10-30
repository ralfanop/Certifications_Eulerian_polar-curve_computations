import EulerianGrothendieck.UniformKernel
import EulerianGrothendieck.RawScaleAsymptotics
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

/-- A single remainder constant for every nonnegative weight bounded by s^k.
In particular, the constant is independent of a parameter entering the weights. -/
theorem geometric_weighted_uniform_all_order_remainder (P : ℕ → ℝ[X])
    (A C s : ℝ) (d R : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hvalues : ∀ M : ℕ, M ≠ 0 → ∀ k, |(P k).eval (1/(M:ℝ))| ≤ 1)
    (hcoeff : ∀ k r, |(P k).coeff r| ≤ A*(r+1)*(C*(k+1:ℝ)^d)^r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℕ → ℝ,
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ s^k) → ∀ M : ℕ, M ≠ 0 →
      |(∑' k, w k*(P k).eval (1/(M:ℝ))) -
        ∑ r ∈ range (R+1), (∑' k, w k*(P k).coeff r)/(M:ℝ)^r| ≤
        K/(M:ℝ)^(R+1) := by
  let K := ∑' k : ℕ, s^k*remainderMajorant A (C*(k+1:ℝ)^d) R
  have hgeom := weighted_remainderMajorant_summable (fun k => s^k) A C s d R
    hA hC hs0 hs1 (fun k => by positivity) (fun k => le_rfl)
  refine ⟨K, tsum_nonneg (fun k => mul_nonneg (by positivity)
    (remainderMajorant_nonneg _ _ _ hA (by positivity))), ?_⟩
  intro w hw hws M hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hwsum : Summable w := (hasSum_geometric_of_lt_one hs0.le hs1).summable.of_norm_bounded
    (fun k => by rw [Real.norm_eq_abs, abs_of_nonneg (hw k)]; exact hws k)
  have hmajor := weighted_remainderMajorant_summable w A C s d R hA hC hs0 hs1 hw hws
  have h := weighted_polynomial_remainder P w (fun k => C*(k+1:ℝ)^d) A (1/(M:ℝ)) R
    hA (by positivity) (by exact (div_le_one (by positivity)).2 hM1) hw (fun k => by positivity)
    (hvalues M hM) hcoeff hwsum
    (fun r => weighted_coefficients_summable P w A C s d r hA hC hs0 hs1 hw hws (fun k => hcoeff k r))
    hmajor
  have hK : (∑' k, w k*remainderMajorant A (C*(k+1:ℝ)^d) R) ≤ K := by
    exact hmajor.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hws k)
      (remainderMajorant_nonneg _ _ _ hA (by positivity))) hgeom
  have he := h.trans (mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ (1/(M:ℝ))^(R+1)))
  simpa only [one_div_pow, mul_one_div] using he

theorem binomialWeight_parameter_bound (t T : ℝ) (ht : 0 ≤ t) (hT : t ≤ T) (k : ℕ) :
    binomialWeight t k ≤ (T^2)^k := by
  apply (binomialWeight_le_geometric t k).trans
  apply pow_le_pow_left₀ (sq_nonneg t)
  nlinarith

/-- Uniform all-order norm remainder on every parameter interval 0<t<=T<1. -/
theorem uniformNormSeries_uniform_parameters (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ T → ∀ M : ℕ, M ≠ 0 →
      |uniformNormSeries M t -
        ∑ r ∈ range (R+1), uniformNormCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K,hK,hrem⟩ := geometric_weighted_uniform_all_order_remainder uniformSquaredPolynomial
    4 128 (T^2) 2 R (by norm_num) (by norm_num) (sq_pos_of_pos hT0) (by nlinarith)
    (fun M hM k => uniformSquaredPolynomial_value_bound M k hM)
    uniformSquaredPolynomial_coefficient_bound
  refine ⟨K,hK,?_⟩
  intro t ht htT M hM
  simpa only [uniformNormSeries, uniformNormCoefficient, uniformSquaredPolynomial_value M _ hM] using
    hrem (binomialWeight t) (binomialWeight_nonneg t) (binomialWeight_parameter_bound t T ht.le htT) M hM

/-- The uniform statement for actual probability integrals, with no extra asymptotic hypothesis. -/
theorem uniform_exponential_integral_uniform_parameters
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ T → ∀ M : ℕ, M ≠ 0 →
      |(∫ xy, Real.exp (t*(standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformNormCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K,hK,hrem⟩ := uniformNormSeries_uniform_parameters T hT0 hT1 R
  refine ⟨K,hK,?_⟩
  intro t ht htT M hM
  rw [uniform_exponential_integral_eq_series U hU hind hlaw M hM t]
  exact hrem t ht htT M hM


/-- Uniformity in the original scale, for all c>=c0>1/12. -/
theorem raw_uniform_kernel_uniform_parameters
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c0 : ℝ) (hc0 : 1/12 < c0) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, c0 ≤ c → ∀ M : ℕ, M ≠ 0 →
      |(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/
        (c*(M:ℝ))) ∂μ.prod μ) -
        ∑ r ∈ range (R+1), uniformNormCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  have hc00 : 0 < c0 := by linarith
  have hT0 : 0 < 1/(12*c0) := by positivity
  have hT1 : 1/(12*c0) < 1 := by
    apply (div_lt_one (by positivity : 0 < 12*c0)).2
    linarith
  obtain ⟨K,hK,hrem⟩ := uniformNormSeries_uniform_parameters (1/(12*c0)) hT0 hT1 R
  refine ⟨K,hK,?_⟩
  intro c hc M hM
  have hcpos : 0 < c := lt_of_lt_of_le hc00 hc
  have ht : 0 < 1/(12*c) := by positivity
  have htT : 1/(12*c) ≤ 1/(12*c0) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 12*c0)
    linarith
  rw [raw_uniform_kernel_identity U hU hind hlaw c (ne_of_gt hcpos) M hM]
  exact hrem (1/(12*c)) ht htT M hM

end EulerianGrothendieck
