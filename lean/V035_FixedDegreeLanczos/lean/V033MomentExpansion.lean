import V033CumulantPolynomials
import V033GaussianAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace V033.UniformSum
open Polynomial Finset MeasureTheory ProbabilityTheory

def evenMomentPolynomial (r : ℕ) : ℝ[X] :=
  C ((2*r).factorial : ℝ) * normalizedEGFPolynomial r

/-- The exact polynomial represents the actual normalized probability moment. -/
theorem actual_normalized_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M r : ℕ) (hM : M ≠ 0) :
    (∫ ω, (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω))^(2*r) ∂μ) =
      (evenMomentPolynomial r).eval (1/(M:ℝ)) := by
  have hm : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hs : (Real.sqrt (12/(M:ℝ)))^2 = 12/(M:ℝ) := Real.sq_sqrt (by positivity)
  simp only [mul_pow, pow_mul, hs]
  simp only [← pow_mul]
  rw [integral_const_mul, (all_sum_moments U hU hind hlaw M (2*r)).2,
    even_moment_coefficient, evenMomentPolynomial, eval_mul, eval_C,
    normalizedEGFPolynomial_exact M r hM]
  ring

theorem actual_normalized_odd_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M r : ℕ) :
    (∫ ω, (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω))^(2*r+1) ∂μ) = 0 := by
  simp only [mul_pow]
  rw [integral_const_mul, (all_sum_moments U hU hind hlaw M (2*r+1)).2,
    sumMoment_odd, mul_zero]

theorem normalized_constant_recurrence (r : ℕ) :
    (normalizedEGFPolynomial (r+1)).coeff 0 =
      (normalizedEGFPolynomial r).coeff 0 / (2*(r+1:ℝ)) := by
  rw [normalizedEGFPolynomial, coeff_C_mul, finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp only [cumulant_zero, pow_one, pow_zero, mul_one, mul_assoc,
      coeff_C_mul, Nat.sub_zero]
    push_cast
    field_simp
    <;> ring
  · intro k hk hk0
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    simp [show ¬ k ≤ 0 by omega]
  · simp

theorem normalized_linear_recurrence (r : ℕ) :
    (normalizedEGFPolynomial (r+2)).coeff 1 =
      ((normalizedEGFPolynomial (r+1)).coeff 1 / 2 -
        (normalizedEGFPolynomial r).coeff 0 / 10) / (r+2:ℝ) := by
  rw [normalizedEGFPolynomial, coeff_C_mul, finset_sum_coeff]
  have hs := Finset.sum_subset (s₁ := ({0,1}:Finset ℕ)) (s₂ := range (r+1+1))
    (f := fun k => (C ((12:ℝ)^(k+1)*cumulantCoefficient k) * X^k *
      normalizedEGFPolynomial (r+1-k)).coeff 1)
    (by intro k hk; simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl|rfl <;> simp)
    (by
      intro k hk hnot
      dsimp only
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      have hk2 : ¬ k ≤ 1 := by simp only [mem_insert, mem_singleton, not_or] at hnot; omega
      simp [hk2])
  rw [← hs]
  simp only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true,
    sum_singleton, Nat.sub_zero, Nat.add_sub_cancel, pow_zero, mul_one,
    pow_one, mul_assoc, coeff_C_mul, coeff_X_mul, cumulant_zero, cumulant_one]
  norm_num
  ring

theorem normalized_constant (r : ℕ) :
    (normalizedEGFPolynomial r).coeff 0 = 1 / ((2:ℝ)^r * (r.factorial:ℝ)) := by
  induction r with
  | zero => simp [normalizedEGFPolynomial]
  | succ r ih =>
    rw [normalized_constant_recurrence, ih, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    <;> ring

#print axioms actual_normalized_even_moment
#print axioms actual_normalized_odd_moment
#print axioms normalized_constant

theorem normalized_linear_initial :
    (normalizedEGFPolynomial 0).coeff 1 = 0 ∧
    (normalizedEGFPolynomial 1).coeff 1 = 0 := by
  norm_num [normalizedEGFPolynomial, cumulant_zero, coeff_one]

theorem normalized_linear (r : ℕ) :
    (normalizedEGFPolynomial (r+2)).coeff 1 =
      -1 / (20 * (2:ℝ)^r * (r.factorial:ℝ)) := by
  induction r with
  | zero =>
    rw [normalized_linear_recurrence, normalized_linear_initial.2, normalized_constant]
    norm_num
  | succ r ih =>
    rw [normalized_linear_recurrence, ih, normalized_constant]
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hf : (r.factorial:ℝ) ≠ 0 := by positivity
    have hr : (r:ℝ)+1 ≠ 0 := by positivity
    have hr2 : (r:ℝ)+1+2 ≠ 0 := by positivity
    field_simp
    <;> ring

theorem even_moment_constant (r : ℕ) :
    (evenMomentPolynomial r).coeff 0 = Gaussian.moment (2*r) := by
  rw [evenMomentPolynomial, coeff_C_mul, normalized_constant]
  induction r with
  | zero => norm_num [Gaussian.moment]
  | succ r ih =>
    rw [show 2*(r+1)=2*r+2 by omega, Gaussian.moment]
    rw [← ih]
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hf : (r.factorial:ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring

theorem even_moment_linear (r : ℕ) :
    (evenMomentPolynomial r).coeff 1 =
      -(1/20:ℝ) * Gaussian.expectation (Gaussian.H 4 * X^(2*r)) := by
  rw [Gaussian.hermite_integration_by_parts]
  rcases r with _ | (_ | r)
  · norm_num [evenMomentPolynomial, normalizedEGFPolynomial, coeff_one]
  · norm_num [evenMomentPolynomial, normalizedEGFPolynomial, cumulant_zero,
      Function.iterate_succ_apply']
  · rw [evenMomentPolynomial, coeff_C_mul, normalized_linear]
    rw [← monomial_one_right_eq_X_pow]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      derivative_monomial]
    rw [Gaussian.expectation_monomial]
    have hn : 2*(r+2)-1-1-1-1 = 2*r := by omega
    rw [hn, ← even_moment_constant, evenMomentPolynomial, coeff_C_mul,
      normalized_constant]
    have h1 : 2*(r+2)-1 = 2*r+3 := by omega
    have h2 : 2*(r+2)-1-1 = 2*r+2 := by omega
    have h3 : 2*(r+2)-1-1-1 = 2*r+1 := by omega
    rw [h3, h2, h1, show 2*(r+2)=2*r+4 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one]
    ring

#print axioms normalized_linear
#print axioms even_moment_constant
#print axioms even_moment_linear
end V033.UniformSum
