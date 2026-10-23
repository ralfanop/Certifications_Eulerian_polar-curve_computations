import V033Core
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-! Arbitrary-degree Gaussian polynomial identities, proved algebraically.
The Gaussian functional is specified by its actual moment recurrence, rather
than by assumptions about orthogonal polynomials or the desired asymptotics. -/
noncomputable section
namespace V033.Gaussian
open Polynomial

def moment : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1 : ℝ) * moment n

def expectation : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => (moment n) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

@[simp] theorem expectation_monomial (n : ℕ) (a : ℝ) :
    expectation (monomial n a) = a * moment n := by
  simp [expectation, Polynomial.lsum, Polynomial.sum_monomial_index, mul_comm]

@[simp] theorem expectation_C (a : ℝ) : expectation (C a) = a := by
  simpa [moment] using expectation_monomial 0 a

@[simp] theorem expectation_one : expectation 1 = 1 := by
  simpa using expectation_C 1

@[simp] theorem expectation_C_mul (a : ℝ) (p : ℝ[X]) :
    expectation (C a * p) = a * expectation p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem moment_succ (n : ℕ) : moment (n+1) = (n:ℝ) * moment (n-1) := by
  cases n with
  | zero => simp [moment]
  | succ n => simp [moment, Nat.cast_add, Nat.cast_one]

/-- Polynomial Gaussian integration by parts (Stein identity). -/
theorem stein (p : ℝ[X]) : expectation (X*p) = expectation p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial n a =>
    rw [X_mul_monomial, derivative_monomial, expectation_monomial,
      expectation_monomial, moment_succ]
    ring

def H (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem H_zero : H 0 = 1 := by simp [H]
@[simp] theorem H_one : H 1 = X := by simp [H, Polynomial.hermite_one]
theorem H_succ (n : ℕ) : H (n+1) = X * H n - (H n).derivative := by
  simp [H, Polynomial.hermite_succ, Polynomial.derivative_map]
@[simp] theorem degree_H (n : ℕ) : (H n).natDegree = n := by
  rw [H, (Polynomial.hermite_monic n).natDegree_map, Polynomial.natDegree_hermite]
theorem monic_H (n : ℕ) : (H n).Monic :=
  (Polynomial.hermite_monic n).map _

/-- Moving a Hermite factor transfers derivatives to the other polynomial. -/
theorem hermite_integration_by_parts (n : ℕ) (p : ℝ[X]) :
    expectation (H n * p) = expectation (derivative^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hs := stein (H n * p)
    rw [derivative_mul, map_add] at hs
    calc
      expectation (H (n+1) * p) = expectation (H n * p.derivative) := by
        rw [H_succ, sub_mul, map_sub, mul_assoc, hs]
        ring
      _ = expectation (derivative^[n] p.derivative) := ih _
      _ = expectation (derivative^[n+1] p) := by rw [Function.iterate_succ_apply]

theorem hermite_orthogonal_lower (n : ℕ) (p : ℝ[X]) (hp : p.natDegree < n) :
    expectation (H n * p) = 0 := by
  rw [hermite_integration_by_parts, iterate_derivative_eq_zero hp, map_zero]

theorem derivative_top_monic (p : ℝ[X]) (hp : p.Monic) :
    derivative^[p.natDegree] p = C (p.natDegree.factorial : ℝ) := by
  ext k
  rw [coeff_iterate_derivative]
  by_cases hk : k = 0
  · subst k
    simp [hp.coeff_natDegree, Nat.descFactorial_self]
  · have hlt : p.natDegree < k+p.natDegree := by omega
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, coeff_C, hk]

/-- The squared monic Hermite norm for every degree. -/
theorem hermite_norm (n : ℕ) : expectation (H n * H n) = (n.factorial : ℝ) := by
  rw [hermite_integration_by_parts]
  have h := derivative_top_monic (H n) (monic_H n)
  simp only [degree_H] at h
  rw [h, expectation_C]

theorem hermite_orthogonal (n m : ℕ) (hnm : n ≠ m) :
    expectation (H n * H m) = 0 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · rw [mul_comm]
    exact hermite_orthogonal_lower m (H n) (by simpa using h)
  · exact hermite_orthogonal_lower n (H m) (by simpa using h)

theorem derivative_H_succ (n : ℕ) :
    (H (n+1)).derivative = C (n+1 : ℝ) * H n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [H_succ (n+1), map_sub, derivative_mul, derivative_X, one_mul,
      ih, derivative_C_mul]
    rw [H_succ n]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem derivative_H (n : ℕ) :
    (H n).derivative = C (n:ℝ) * H (n-1) := by
  cases n with
  | zero => simp
  | succ n => simpa using derivative_H_succ n

theorem iterate_derivative_H (n k : ℕ) (hkn : k ≤ n) :
    derivative^[k] (H n) = C (n.descFactorial k : ℝ) * H (n-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), derivative_C_mul, derivative_H]
    rw [Nat.descFactorial_succ]
    have hsub : n-k-1 = n-(k+1) := by omega
    rw [hsub, Nat.cast_mul, map_mul, Nat.cast_sub (by omega)]
    ring

theorem derivative_cross_zero (n a b : ℕ) (hab : a ≠ b) :
    expectation ((derivative^[a] (H n)) * (derivative^[b] (H n))) = 0 := by
  by_cases ha : a ≤ n
  · by_cases hb : b ≤ n
    · rw [iterate_derivative_H n a ha, iterate_derivative_H n b hb]
      rw [show C (n.descFactorial a : ℝ) * H (n-a) *
          (C (n.descFactorial b : ℝ) * H (n-b)) =
          C ((n.descFactorial a : ℝ) * n.descFactorial b) *
          (H (n-a) * H (n-b)) by rw [map_mul]; ring]
      rw [expectation_C_mul, hermite_orthogonal _ _ (by omega), mul_zero]
    · rw [iterate_derivative_eq_zero (p := H n) (x := b) (by simpa using Nat.lt_of_not_ge hb)]
      simp
  · rw [iterate_derivative_eq_zero (p := H n) (x := a) (by simpa using Nat.lt_of_not_ge ha)]
    simp

theorem second_derivative_norm (n : ℕ) :
    expectation ((derivative^[2] (H n)) * (derivative^[2] (H n))) =
      (n:ℝ) * (n-1) * (n.factorial:ℝ) := by
  rcases n with _ | (_ | n)
  · simp [Function.iterate_succ_apply']
  · simp [Function.iterate_succ_apply']
  · rw [iterate_derivative_H (n+2) 2 (by omega)]
    rw [show C ((n+2).descFactorial 2 : ℝ) * H (n+2-2) *
        (C ((n+2).descFactorial 2 : ℝ) * H (n+2-2)) =
        C (((n+2).descFactorial 2 : ℝ)^2) * (H n * H n) by
          simp only [Nat.add_sub_cancel]; rw [map_pow]; ring]
    rw [expectation_C_mul, hermite_norm]
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    norm_num
    ring

/-- The first perturbation coefficient used in the all-degree theorem. -/
theorem fourth_hermite_mixed_norm (n : ℕ) :
    expectation (H 4 * (H n * H n)) = 6*(n:ℝ)*(n-1)*(n.factorial:ℝ) := by
  rw [hermite_integration_by_parts, iterate_derivative_mul, map_sum]
  rw [Finset.sum_eq_single 2]
  · rw [map_nsmul, show (4:ℕ).choose 2 = 6 by decide, nsmul_eq_mul]
    change (6:ℝ) * expectation ((derivative^[2] (H n)) * (derivative^[2] (H n))) = _
    rw [second_derivative_norm]
    ring
  · intro k hk hk2
    rw [map_nsmul, derivative_cross_zero n (4-k) k (by
      have hk4 := Finset.mem_range.mp hk
      omega)]
    simp
  · simp

#print axioms fourth_hermite_mixed_norm
#print axioms stein
#print axioms hermite_integration_by_parts
#print axioms hermite_norm
#print axioms hermite_orthogonal
end V033.Gaussian
