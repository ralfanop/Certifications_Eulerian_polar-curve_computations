import V033GramExpansion
import V033GramBasis

noncomputable section
namespace V033.UniformSum
open Polynomial Finset MeasureTheory ProbabilityTheory Matrix

def functional (t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ := (Polynomial.leval t).comp momentMap
def rawFunctional (M : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => sumMoment M n • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

@[simp] theorem rawFunctional_monomial (M n : ℕ) (a : ℝ) :
    rawFunctional M (monomial n a) = a*sumMoment M n := by
  simp [rawFunctional, Polynomial.lsum, Polynomial.sum_monomial_index, mul_comm]
@[simp] theorem rawFunctional_X_pow (M n : ℕ) :
    rawFunctional M (X^n) = sumMoment M n := by
  rw [← monomial_one_right_eq_X_pow, rawFunctional_monomial, one_mul]

@[simp] theorem functional_apply (t : ℝ) (p : ℝ[X]) :
    functional t p = (momentMap p).eval t := rfl

theorem rawFunctional_actual {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M : ℕ) (p : ℝ[X]) :
    Integrable (fun ω => p.eval (∑ i ∈ range M, U i ω)) μ ∧
      (∫ ω, p.eval (∑ i ∈ range M, U i ω) ∂μ) = rawFunctional M p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    constructor
    · simpa only [eval_add] using hp.1.add hq.1
    · simp only [eval_add, integral_add hp.1 hq.1, map_add, hp.2, hq.2]
  | monomial n a =>
    have h := all_sum_moments U hU hind hlaw M n
    constructor
    · simpa only [eval_monomial] using h.1.const_mul a
    · rw [rawFunctional_monomial]
      simp only [eval_monomial, integral_const_mul, h.2]

theorem functional_actual {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M : ℕ) (hM : M ≠ 0) (p : ℝ[X]) :
    Integrable (fun ω => p.eval (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω))) μ ∧
      (∫ ω, p.eval (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω)) ∂μ) =
        functional (1/(M:ℝ)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    constructor
    · simpa only [eval_add] using hp.1.add hq.1
    · simp only [eval_add, integral_add hp.1 hq.1, map_add, hp.2, hq.2]
  | monomial n a =>
    have hi : Integrable (fun ω => (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω))^n) μ := by
      simpa only [mul_pow] using
        ((all_sum_moments U hU hind hlaw M n).1.const_mul (Real.sqrt (12/(M:ℝ))^n))
    constructor
    · simpa only [eval_monomial] using hi.const_mul a
    · simp only [eval_monomial, integral_const_mul, functional_apply,
        momentMap_monomial, eval_mul, eval_C]
      rw [actual_moment U hU hind hlaw M n hM]

theorem determinant_is_hankel (n : ℕ) (t : ℝ) :
    (determinantPolynomial n).eval t = (Gram.hankel (functional t) n).det := by
  have h := Gram.monic_gram_det (functional t) (fun i : Fin n => Gaussian.H i.val)
    (fun i => Gaussian.degree_H _) (fun i => Gaussian.monic_H _)
  rw [determinantPolynomial, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  exact h

def scalingProduct (a : ℝ) (n : ℕ) : ℝ := ∏ i : Fin n, a^i.val

theorem scalingProduct_succ (a : ℝ) (n : ℕ) :
    scalingProduct a (n+1) = scalingProduct a n * a^n := by
  unfold scalingProduct
  rw [Fin.prod_univ_castSucc]
  rfl

theorem scalingProduct_ne_zero (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    scalingProduct a n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ ha

theorem moment_scaling (M n : ℕ) (hM : M ≠ 0) :
    functional (1/(M:ℝ)) (X^n) = Real.sqrt (12/(M:ℝ))^n * rawFunctional M (X^n) := by
  rw [functional_apply, momentMap_X_pow, rawFunctional_X_pow]
  rcases Nat.even_or_odd n with hn|hn
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r by omega, momentPolynomial_even, evenMomentPolynomial,
      eval_mul, eval_C, normalizedEGFPolynomial_exact M r hM,
      pow_mul, Real.sq_sqrt (by positivity), even_moment_coefficient]
    ring
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r+1 by omega, momentPolynomial_odd, eval_zero, sumMoment_odd, mul_zero]

theorem hankel_scaling (M n : ℕ) (hM : M ≠ 0) :
    (determinantPolynomial n).eval (1/(M:ℝ)) =
      (scalingProduct (Real.sqrt (12/(M:ℝ))) n)^2 * (Gram.hankel (rawFunctional M) n).det := by
  let A := diagonal (fun i : Fin n => Real.sqrt (12/(M:ℝ))^i.val)
  have he : Gram.hankel (functional (1/(M:ℝ))) n =
      A * Gram.hankel (rawFunctional M) n * A := by
    ext i j
    dsimp [A]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    change functional (1/(M:ℝ)) (X^(i.val+j.val)) =
      Real.sqrt (12/(M:ℝ))^i.val * rawFunctional M (X^(i.val+j.val)) * Real.sqrt (12/(M:ℝ))^j.val
    rw [moment_scaling M _ hM, pow_add]
    ring
  rw [determinant_is_hankel, he, det_mul, det_mul]
  have hd : A.det = scalingProduct (Real.sqrt (12/(M:ℝ))) n := det_diagonal
  rw [hd]
  ring

#print axioms rawFunctional_actual
#print axioms functional_actual
#print axioms hankel_scaling
end V033.UniformSum
