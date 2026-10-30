import V033CumulantPolynomials
import EulerianGrothendieck.FiniteSeries
import EulerianGrothendieck.Probability
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Actual uniform-sum probability moments, finite moment polynomials, and
coefficientwise Gaussian domination. No asymptotic estimate is assumed. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory PowerSeries Polynomial

namespace EulerianGrothendieck

def uniformEGFCoefficient (k : ℕ) : ℝ := 3^k / ((2*k+1).factorial : ℝ)
def gaussianEGFCoefficient (k : ℕ) : ℝ := 1 / (2^k * (k.factorial : ℝ))

theorem momentFactor_factorial (k : ℕ) :
    momentFactor k = 6^k * (k.factorial : ℝ) / ((2*k+1).factorial : ℝ) := by
  induction k with
  | zero => norm_num [momentFactor]
  | succ k ih =>
    rw [momentFactor, ih]
    rw [show 2*(k+1)+1 = (2*k+1)+2 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : ((2*k+1).factorial : ℝ) ≠ 0 := by positivity
    have hd : (2*(k:ℝ)+3) ≠ 0 := by positivity
    have hd' : (2*(k:ℝ)+2) ≠ 0 := by positivity
    push_cast
    field_simp
    <;> ring

theorem uniformEGFCoefficient_factor (k : ℕ) :
    uniformEGFCoefficient k = momentFactor k * gaussianEGFCoefficient k := by
  rw [uniformEGFCoefficient, gaussianEGFCoefficient, momentFactor_factorial]
  have hp : (6:ℝ)^k = 2^k * 3^k := by rw [← mul_pow]; norm_num
  rw [hp]
  field_simp

theorem uniformEGFCoefficient_nonneg (k : ℕ) : 0 ≤ uniformEGFCoefficient k := by
  unfold uniformEGFCoefficient
  positivity

theorem uniformEGFCoefficient_le_gaussian (k : ℕ) :
    uniformEGFCoefficient k ≤ gaussianEGFCoefficient k := by
  rw [uniformEGFCoefficient_factor]
  exact mul_le_of_le_one_left (by unfold gaussianEGFCoefficient; positivity)
    (momentFactor_le_one k)

theorem coeffPower_eq_powerSeries (a : ℕ → ℝ) (M k : ℕ) :
    coeffPower a M k = PowerSeries.coeff k ((PowerSeries.mk a)^M) := by
  induction M generalizing k with
  | zero =>
    simp only [coeffPower, pow_zero, PowerSeries.coeff_one]
  | succ M ih =>
    rw [coeffPower, pow_succ', PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun j l => PowerSeries.coeff j (PowerSeries.mk a) *
          PowerSeries.coeff l ((PowerSeries.mk a)^M)) k]
    apply Finset.sum_congr rfl
    intro j hj
    rw [PowerSeries.coeff_mk, ih]

theorem gaussianEGF_series :
    PowerSeries.mk gaussianEGFCoefficient =
      PowerSeries.rescale (1/2:ℝ) (PowerSeries.exp ℝ) := by
  ext k
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [gaussianEGFCoefficient, div_pow, map_div₀, map_natCast, map_one]
  ring

theorem gaussianEGF_power (M k : ℕ) :
    coeffPower gaussianEGFCoefficient M k = (M:ℝ)^k / (2^k*(k.factorial:ℝ)) := by
  rw [coeffPower_eq_powerSeries, gaussianEGF_series, ← map_pow,
    PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [gaussianEGFCoefficient, mul_pow, div_pow, map_div₀, map_natCast, map_one]
  ring

def uniformMomentRatio (M k : ℕ) : ℝ :=
  (2^k*(k.factorial:ℝ)/(M:ℝ)^k) * coeffPower uniformEGFCoefficient M k

theorem uniformMomentRatio_nonneg (M k : ℕ) : 0 ≤ uniformMomentRatio M k := by
  apply mul_nonneg
  · positivity
  · exact coeffPower_nonneg _ uniformEGFCoefficient_nonneg M k

theorem uniformMomentRatio_le_one (M k : ℕ) (hM : M ≠ 0) :
    uniformMomentRatio M k ≤ 1 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  calc
    uniformMomentRatio M k ≤
        (2^k*(k.factorial:ℝ)/(M:ℝ)^k) * coeffPower gaussianEGFCoefficient M k := by
      apply mul_le_mul_of_nonneg_left
      · exact coeffPower_mono _ _ uniformEGFCoefficient_nonneg
          (fun k => by unfold gaussianEGFCoefficient; positivity)
          uniformEGFCoefficient_le_gaussian M k
      · positivity
    _ = 1 := by rw [gaussianEGF_power]; field_simp

theorem uniformEGF_series :
    PowerSeries.mk uniformEGFCoefficient =
      PowerSeries.rescale (12:ℝ) V033.UniformSum.evenEGF := by
  ext k
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    V033.UniformSum.evenEGF_coeff, V033.UniformSum.singleMoment_even]
  unfold uniformEGFCoefficient
  rw [Nat.factorial_succ]
  push_cast
  have hp : (12:ℝ)^k = 3^k*4^k := by rw [← mul_pow]; norm_num
  rw [hp]
  field_simp
  <;> ring

def uniformRatioPolynomial (k : ℕ) : ℝ[X] :=
  Polynomial.C (2^k*(k.factorial:ℝ)) * V033.UniformSum.normalizedEGFPolynomial k

theorem uniformMomentRatio_exact_polynomial (M k : ℕ) (hM : M ≠ 0) :
    uniformMomentRatio M k = (uniformRatioPolynomial k).eval (1/(M:ℝ)) := by
  rw [uniformMomentRatio, coeffPower_eq_powerSeries, uniformEGF_series,
    ← map_pow, PowerSeries.coeff_rescale, uniformRatioPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C,
    V033.UniformSum.normalizedEGFPolynomial_exact M k hM, div_pow]
  ring

theorem actual_uniform_sum_moment_ratio
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (M k : ℕ) (hM : M ≠ 0) :
    (∫ ω, (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ Finset.range M, U i ω))^(2*k) ∂μ) /
      (((2*k).factorial:ℝ)/(2^k*(k.factorial:ℝ))) = uniformMomentRatio M k := by
  have hs : (Real.sqrt (12/(M:ℝ)))^2 = 12/(M:ℝ) := Real.sq_sqrt (by positivity)
  simp only [mul_pow, pow_mul, hs]
  simp only [← pow_mul]
  rw [integral_const_mul, (V033.UniformSum.all_sum_moments U hU hind hlaw M (2*k)).2,
    V033.UniformSum.even_moment_coefficient, uniformMomentRatio_exact_polynomial M k hM,
    uniformRatioPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    V033.UniformSum.normalizedEGFPolynomial_exact M k hM]
  field_simp
  <;> ring

end EulerianGrothendieck
