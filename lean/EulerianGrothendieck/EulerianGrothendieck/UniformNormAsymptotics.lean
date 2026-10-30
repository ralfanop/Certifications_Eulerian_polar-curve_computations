import EulerianGrothendieck.UniformRatioBounds
import EulerianGrothendieck.GeometricSummability
import Mathlib.Data.Nat.Choose.Bounds

/-! Arbitrary finite-order expansion of the actual normalized uniform-moment
series. The all-index bound and the infinite-sum remainder are proved upstream.
No coefficient or remainder estimate is a hypothesis of the final theorem. -/
noncomputable section
open scoped BigOperators
open Finset Polynomial MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

def binomialWeight (t : ℝ) (k : ℕ) : ℝ :=
  (((2*k).choose k:ℝ)/4^k)*t^(2*k)

def uniformSquaredPolynomial (k : ℕ) : ℝ[X] := (uniformRatioPolynomial k)^2

def uniformNormSeries (M : ℕ) (t : ℝ) : ℝ :=
  ∑' k, binomialWeight t k*(uniformMomentRatio M k)^2

def uniformNormCoefficient (t : ℝ) (r : ℕ) : ℝ :=
  ∑' k, binomialWeight t k*(uniformSquaredPolynomial k).coeff r

theorem binomialWeight_nonneg (t : ℝ) (k : ℕ) : 0 ≤ binomialWeight t k := by
  unfold binomialWeight
  apply mul_nonneg (by positivity)
  rw [pow_mul]
  positivity

theorem binomialWeight_le_geometric (t : ℝ) (k : ℕ) :
    binomialWeight t k ≤ (t^2)^k := by
  have hc : ((2*k).choose k:ℝ) ≤ (4:ℝ)^k := by
    have h := Nat.choose_le_two_pow (2*k) k
    have he : (2:ℕ)^(2*k)=4^k := by rw [pow_mul]; norm_num
    rw [he] at h
    exact_mod_cast h
  unfold binomialWeight
  rw [pow_mul]
  apply mul_le_of_le_one_left (by positivity)
  exact (div_le_one (by positivity)).2 hc

theorem uniformSquaredPolynomial_coefficient_bound (k r : ℕ) :
    |(uniformSquaredPolynomial k).coeff r| ≤ 4*(r+1)*(128*(k+1:ℝ)^2)^r := by
  unfold uniformSquaredPolynomial
  rw [pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j l => (uniformRatioPolynomial k).coeff j*(uniformRatioPolynomial k).coeff l) r]
  have h := convolution_coefficient_bound (fun j => (uniformRatioPolynomial k).coeff j)
    2 (128*(k+1:ℝ)^2) (by norm_num) (by positivity)
    (uniformRatio_coefficient_bound k) r
  norm_num only [show (2:ℝ)^2 = 4 by norm_num] at h
  simpa [coeffConv, mul_comm, mul_left_comm, mul_assoc] using h

theorem uniformSquaredPolynomial_value (M k : ℕ) (hM : M ≠ 0) :
    (uniformSquaredPolynomial k).eval (1/(M:ℝ)) = (uniformMomentRatio M k)^2 := by
  rw [uniformSquaredPolynomial, Polynomial.eval_pow, uniformMomentRatio_exact_polynomial M k hM]

theorem uniformSquaredPolynomial_value_bound (M k : ℕ) (hM : M ≠ 0) :
    |(uniformSquaredPolynomial k).eval (1/(M:ℝ))| ≤ 1 := by
  rw [uniformSquaredPolynomial_value M k hM, abs_of_nonneg (sq_nonneg _)]
  have h0 := uniformMomentRatio_nonneg M k
  have h1 := uniformMomentRatio_le_one M k hM
  nlinarith

theorem uniformNormCoefficient_absolute_summability (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (r : ℕ) : Summable (fun k => |binomialWeight t k*(uniformSquaredPolynomial k).coeff r|) := by
  apply Summable.abs
  exact weighted_coefficients_summable uniformSquaredPolynomial (binomialWeight t)
    4 128 (t^2) 2 r (by norm_num) (by norm_num) (sq_pos_of_pos ht0)
    (by nlinarith) (binomialWeight_nonneg t) (binomialWeight_le_geometric t)
    (fun k => uniformSquaredPolynomial_coefficient_bound k r)

/-- All orders, all positive integer M, and a remainder constant independent
of M. This theorem is about the exact uniform moment series, not floating-point
samples or a finite list of coefficients. -/
theorem uniformNormSeries_all_orders (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |uniformNormSeries M t -
        ∑ r ∈ range (R+1), uniformNormCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  have h := geometric_weighted_all_order_remainder uniformSquaredPolynomial (binomialWeight t)
    4 128 (t^2) 2 R (by norm_num) (by norm_num) (sq_pos_of_pos ht0)
    (by nlinarith) (binomialWeight_nonneg t) (binomialWeight_le_geometric t)
    (fun M hM k => uniformSquaredPolynomial_value_bound M k hM)
    uniformSquaredPolynomial_coefficient_bound
  obtain ⟨K, hK, hrem⟩ := h
  refine ⟨K, hK, ?_⟩
  intro M hM
  simpa only [uniformNormSeries, uniformNormCoefficient, uniformSquaredPolynomial_value M _ hM] using hrem M hM

/-- The same all-order conclusion for the moments expressed as probability
integrals of an actual independent uniform sequence. -/
theorem actual_uniform_moment_series_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |(∑' k, binomialWeight t k *
        ((∫ ω, (Real.sqrt (12/(M:ℝ))*(∑ i ∈ range M, U i ω))^(2*k) ∂μ) /
          (((2*k).factorial:ℝ)/(2^k*(k.factorial:ℝ))))^2) -
        ∑ r ∈ range (R+1), uniformNormCoefficient t r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := uniformNormSeries_all_orders t ht0 ht1 R
  refine ⟨K, hK, ?_⟩
  intro M hM
  simpa only [actual_uniform_sum_moment_ratio U hU hind hlaw M _ hM, uniformNormSeries] using hrem M hM

end EulerianGrothendieck
