import EulerianGrothendieck.UniformFirstCorrection
import EulerianGrothendieck.CentralBinomialMoments

noncomputable section
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

theorem uniformNormCoefficient_one_closed (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    uniformNormCoefficient t 1 = -(3/10:ℝ)*t^4*(1/Real.sqrt (1-t^2))^5 := by
  have h := (centralBinomial_second_factorial_moment_hasSum (t^2) (sq_nonneg t)
    (by nlinarith)).mul_left (-2/5:ℝ)
  have he : ∀ k, binomialWeight t k*(uniformSquaredPolynomial k).coeff 1 =
      (-2/5:ℝ)*((k:ℝ)*(k-1)*centralCoefficient k*(t^2)^k) := by
    intro k
    rw [uniformSquaredPolynomial_first_coefficient]
    simp only [binomialWeight, centralCoefficient, Nat.centralBinom, pow_mul]
    ring
  unfold uniformNormCoefficient
  simp_rw [he]
  rw [h.tsum_eq]
  ring

theorem inverseSeriesCoefficient_zero (b : ℕ → ℝ) : inverseSeriesCoefficient b 0 = (b 0)⁻¹ := by
  simp [inverseSeriesCoefficient, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_inv]

theorem inverseSeriesCoefficient_one_relation (b : ℕ → ℝ) (hb : b 0 ≠ 0) :
    b 0*inverseSeriesCoefficient b 1 + b 1*inverseSeriesCoefficient b 0 = 0 := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) 1)
    (PowerSeries.mul_inv_cancel (PowerSeries.mk b) (by simpa using hb))
  rw [PowerSeries.coeff_one_mul] at h
  simpa [inverseSeriesCoefficient, PowerSeries.coeff_zero_eq_constantCoeff, mul_comm, add_comm] using h

theorem uniformVacuumCoefficient_zero_closed (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    uniformVacuumCoefficient t 0 = Real.sqrt (1-t^2) := by
  rw [uniformVacuumCoefficient, inverseSeriesCoefficient_zero,
    uniformNormCoefficient_zero_closed t ht0 ht1]
  simp

theorem uniformVacuumCoefficient_one_closed (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    uniformVacuumCoefficient t 1 = 3*t^4/(10*(Real.sqrt (1-t^2))^3) := by
  have hd : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 (by nlinarith)
  have h := inverseSeriesCoefficient_one_relation (uniformNormCoefficient t)
    (by have H := uniformNormCoefficient_zero_ge_one t ht0 ht1; linarith)
  change uniformNormCoefficient t 0*uniformVacuumCoefficient t 1 +
    uniformNormCoefficient t 1*uniformVacuumCoefficient t 0 = 0 at h
  rw [uniformNormCoefficient_zero_closed t ht0 ht1,
    uniformNormCoefficient_one_closed t ht0 ht1,
    uniformVacuumCoefficient_zero_closed t ht0 ht1] at h
  field_simp at h ⊢
  nlinarith

/-- The first-order correction including its sign and a proved M^-2 remainder. -/
theorem uniformVacuum_first_order (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(uniformNormSeries M t) -
        Real.sqrt (1-t^2)*(1+(3*t^4/(10*(1-t^2)^2))/(M:ℝ))| ≤ K/(M:ℝ)^2 := by
  obtain ⟨K, hK, hrem⟩ := uniformVacuumSeries_all_orders t ht0 ht1 1
  refine ⟨K, hK, ?_⟩
  intro M hM
  have h := hrem M hM
  have hd : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 (by nlinarith)
  have hs : (Real.sqrt (1-t^2))^2 = 1-t^2 := Real.sq_sqrt (by nlinarith)
  have hcoef : uniformVacuumCoefficient t 1 =
      Real.sqrt (1-t^2)*(3*t^4/(10*(1-t^2)^2)) := by
    have hs4 : (1-t^2)^2 = (Real.sqrt (1-t^2))^4 := by
      calc
        _ = ((Real.sqrt (1-t^2))^2)^2 := congrArg (fun x : ℝ => x^2) hs.symm
        _ = _ := by ring
    rw [uniformVacuumCoefficient_one_closed t ht0 ht1, hs4]
    field_simp
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, div_one,
    pow_one, show (1:ℕ)+1=2 by rfl] at h
  rw [uniformVacuumCoefficient_zero_closed t ht0 ht1, hcoef] at h
  convert h using 1 <;> congr 1 <;> ring

theorem actual_uniform_vacuum_first_order
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |1/(∫ xy, Real.exp (t*(standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2)) ∂μ.prod μ) -
        Real.sqrt (1-t^2)*(1+(3*t^4/(10*(1-t^2)^2))/(M:ℝ))| ≤ K/(M:ℝ)^2 := by
  obtain ⟨K, hK, hrem⟩ := uniformVacuum_first_order t ht0 ht1
  refine ⟨K, hK, ?_⟩
  intro M hM
  rw [uniform_exponential_integral_eq_series U hU hind hlaw M hM t]
  exact hrem M hM

end EulerianGrothendieck
