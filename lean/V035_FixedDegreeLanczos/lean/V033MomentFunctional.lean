import V033MomentExpansion
import V033GaussianGram

noncomputable section
namespace V033.UniformSum
open Polynomial Finset MeasureTheory ProbabilityTheory

def momentPolynomial (n : ℕ) : ℝ[X] :=
  if n % 2 = 0 then evenMomentPolynomial (n/2) else 0

@[simp] theorem momentPolynomial_even (r : ℕ) :
    momentPolynomial (2*r) = evenMomentPolynomial r := by simp [momentPolynomial]
@[simp] theorem momentPolynomial_odd (r : ℕ) :
    momentPolynomial (2*r+1) = 0 := by simp [momentPolynomial, Nat.add_div]

theorem gaussian_moment_odd (r : ℕ) : Gaussian.moment (2*r+1) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [show 2*(r+1)+1 = (2*r+1)+2 by omega, Gaussian.moment, ih, mul_zero]

theorem H4_explicit : Gaussian.H 4 = X^4 - C 6 * X^2 + C 3 := by
  norm_num [Gaussian.H_succ, Gaussian.H_zero, derivative_pow]
  simp only [map_ofNat]
  ring

@[simp] theorem gaussian_expectation_X_pow (n : ℕ) :
    Gaussian.expectation (X^n) = Gaussian.moment n := by
  rw [← monomial_one_right_eq_X_pow, Gaussian.expectation_monomial, one_mul]

theorem gaussian_H4_odd (r : ℕ) :
    Gaussian.expectation (Gaussian.H 4 * X^(2*r+1)) = 0 := by
  rw [H4_explicit, add_mul, sub_mul, map_add, map_sub]
  rw [mul_assoc, ← pow_add, ← pow_add, Gaussian.expectation_C_mul,
    Gaussian.expectation_C_mul, gaussian_expectation_X_pow,
    gaussian_expectation_X_pow, gaussian_expectation_X_pow]
  rw [show 4+(2*r+1) = 2*(r+2)+1 by omega,
      show 2+(2*r+1) = 2*(r+1)+1 by omega]
  simp [gaussian_moment_odd]

theorem moment_constant (n : ℕ) :
    (momentPolynomial n).coeff 0 = Gaussian.moment n := by
  rcases Nat.even_or_odd n with hn|hn
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r by omega, momentPolynomial_even, even_moment_constant]
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r+1 by omega, momentPolynomial_odd, coeff_zero, gaussian_moment_odd]

theorem moment_linear (n : ℕ) :
    (momentPolynomial n).coeff 1 =
      -(1/20:ℝ)*Gaussian.expectation (Gaussian.H 4 * X^n) := by
  rcases Nat.even_or_odd n with hn|hn
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r by omega, momentPolynomial_even, even_moment_linear]
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r+1 by omega, momentPolynomial_odd, coeff_zero, gaussian_H4_odd, mul_zero]

def momentMap : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum (fun n => LinearMap.toSpanSingleton ℝ ℝ[X] (momentPolynomial n))

@[simp] theorem momentMap_monomial (n : ℕ) (a : ℝ) :
    momentMap (monomial n a) = C a * momentPolynomial n := by
  simp [momentMap, Polynomial.lsum, Polynomial.sum_monomial_index,
    LinearMap.toSpanSingleton, Polynomial.smul_eq_C_mul]

theorem momentMap_constant (p : ℝ[X]) : (momentMap p).coeff 0 = Gaussian.expectation p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n a =>
    rw [momentMap_monomial, coeff_C_mul, moment_constant, Gaussian.expectation_monomial]

theorem momentMap_linear (p : ℝ[X]) :
    (momentMap p).coeff 1 = -(1/20:ℝ)*Gaussian.expectation (Gaussian.H 4*p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    rw [momentMap_monomial, coeff_C_mul, moment_linear]
    rw [show monomial n a = C a * X^n by rw [C_mul_X_pow_eq_monomial]]
    rw [show Gaussian.H 4 * (C a * X^n) = C a * (Gaussian.H 4 * X^n) by ring,
      Gaussian.expectation_C_mul]
    ring

@[simp] theorem momentMap_C_mul (a : ℝ) (p : ℝ[X]) :
    momentMap (C a*p) = C a * momentMap p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

@[simp] theorem momentMap_X_pow (n : ℕ) : momentMap (X^n) = momentPolynomial n := by
  rw [← monomial_one_right_eq_X_pow, momentMap_monomial, map_one, one_mul]

theorem actual_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M n : ℕ) (hM : M ≠ 0) :
    (∫ ω, (Real.sqrt (12/(M:ℝ)) * (∑ i ∈ range M, U i ω))^n ∂μ) =
      (momentPolynomial n).eval (1/(M:ℝ)) := by
  rcases Nat.even_or_odd n with hn|hn
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r by omega, momentPolynomial_even]
    exact actual_normalized_even_moment U hU hind hlaw M r hM
  · obtain ⟨r,hr⟩ := hn
    rw [show n=2*r+1 by omega, momentPolynomial_odd, eval_zero]
    exact actual_normalized_odd_moment U hU hind hlaw M r

#print axioms momentMap_linear
#print axioms actual_moment
end V033.UniformSum
