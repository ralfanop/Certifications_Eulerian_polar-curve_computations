import V033UniformSumMoments
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Cast

/-! Finite algebraic construction of the scaled moment polynomials.
All generating series here are formal; no analytic or Edgeworth assertion is used. -/
noncomputable section
namespace V033.UniformSum
open Finset PowerSeries

theorem sumMoment_odd (M r : ℕ) : sumMoment M (2*r+1) = 0 := by
  induction M generalizing r with
  | zero => simp [sumMoment]
  | succ M ih =>
    rw [sumMoment]
    apply Finset.sum_eq_zero
    intro k hk
    have hkbound := Finset.mem_range.mp hk
    rcases Nat.even_or_odd k with ⟨a, ha⟩ | ⟨a, ha⟩
    · have he : 2*r+1-k = 2*(r-a)+1 := by omega
      rw [he, singleMoment_odd]
      ring
    · have he : k = 2*a+1 := by omega
      rw [he, ih]
      ring

theorem sum_range_even (f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ k, f (2*k+1) = 0) :
    (∑ k ∈ range (2*n+1), f k) = ∑ k ∈ range (n+1), f (2*k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega,
      sum_range_succ, sum_range_succ, hf, add_zero, ih]
    conv_rhs => rw [sum_range_succ]
    congr 1

theorem sumMoment_even_succ (M r : ℕ) :
    sumMoment (M+1) (2*r) = ∑ k ∈ range (r+1),
      sumMoment M (2*k) * singleMoment (2*(r-k)) * ((2*r).choose (2*k):ℝ) := by
  rw [sumMoment, sum_range_even _ r (by intro k; rw [sumMoment_odd]; ring)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.mul_sub_left_distrib]

/-- Exponential generating series with the even degree recorded by one index. -/
def evenEGF : PowerSeries ℝ :=
  PowerSeries.mk (fun r => singleMoment (2*r) / ((2*r).factorial : ℝ))

@[simp] theorem evenEGF_coeff (r : ℕ) :
    PowerSeries.coeff r evenEGF = singleMoment (2*r) / ((2*r).factorial : ℝ) :=
  PowerSeries.coeff_mk _ _

@[simp] theorem evenEGF_constant : PowerSeries.constantCoeff evenEGF = 1 := by
  rw [evenEGF, PowerSeries.constantCoeff_mk]
  norm_num

/-- Exact all-order bridge from the probability moments to powers of the uniform EGF. -/
theorem even_moment_coefficient (M r : ℕ) :
    sumMoment M (2*r) = ((2*r).factorial:ℝ) * PowerSeries.coeff r (evenEGF^M) := by
  induction M generalizing r with
  | zero =>
    by_cases hr : r=0
    · subst r; norm_num [sumMoment]
    · simp [sumMoment, hr, PowerSeries.coeff_one]
  | succ M ih =>
    rw [sumMoment_even_succ, pow_succ, PowerSeries.coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l => PowerSeries.coeff k (evenEGF^M) * PowerSeries.coeff l evenEGF) r,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have h2 : 2*k ≤ 2*r := by omega
    rw [ih, evenEGF_coeff, Nat.cast_choose ℝ h2, ← Nat.mul_sub_left_distrib]
    have hf1 : ((2*k).factorial:ℝ) ≠ 0 := by positivity
    have hf2 : ((2*(r-k)).factorial:ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Logarithmic derivative coefficients are cumulants with factorials removed. -/
def cumulantSeries : PowerSeries ℝ := PowerSeries.derivative ℝ evenEGF * evenEGF⁻¹
def cumulantCoefficient (k : ℕ) : ℝ := PowerSeries.coeff k cumulantSeries

theorem cumulant_identity : cumulantSeries * evenEGF = PowerSeries.derivative ℝ evenEGF := by
  rw [cumulantSeries, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

theorem cumulant_zero : cumulantCoefficient 0 = (1:ℝ)/24 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℝ)) cumulant_identity
  rw [map_mul, evenEGF_constant, mul_one] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at h
  norm_num [evenEGF_coeff] at h
  simpa [cumulantCoefficient, PowerSeries.coeff_zero_eq_constantCoeff] using h

theorem cumulant_one : cumulantCoefficient 1 = -(1:ℝ)/1440 := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) 1) cumulant_identity
  rw [PowerSeries.coeff_one_mul, PowerSeries.coeff_derivative] at h
  have hc0 : PowerSeries.constantCoeff cumulantSeries = 1/24 := by
    simpa [cumulantCoefficient, PowerSeries.coeff_zero_eq_constantCoeff] using cumulant_zero
  norm_num [evenEGF_constant, evenEGF_coeff, hc0, Nat.factorial] at h
  change cumulantCoefficient 1 + _ = _ at h
  linarith

/-- This exact polynomial will represent E[Y_M^(2r)]/(2r)!. -/
def normalizedEGFPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | r+1 => Polynomial.C ((r+1:ℝ)⁻¹) *
      ∑ k ∈ range (r+1),
      Polynomial.C ((12:ℝ)^(k+1) * cumulantCoefficient k) *
        Polynomial.X^k * normalizedEGFPolynomial (r-k)
termination_by r => r
decreasing_by omega

theorem power_derivative (M : ℕ) :
    PowerSeries.derivative ℝ (evenEGF^M) =
      PowerSeries.C (M:ℝ) * (cumulantSeries * evenEGF^M) := by
  cases M with
  | zero => simp
  | succ M =>
    rw [Derivation.leibniz_pow, ← cumulant_identity]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul,
      Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one, pow_succ]
    ring

theorem power_coefficient_recurrence (M r : ℕ) :
    PowerSeries.coeff (r+1) (evenEGF^M) * (r+1:ℝ) =
      (M:ℝ) * ∑ k ∈ range (r+1),
        cumulantCoefficient k * PowerSeries.coeff (r-k) (evenEGF^M) := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) r) (power_derivative M)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => PowerSeries.coeff k cumulantSeries * PowerSeries.coeff l (evenEGF^M)) r] at h
  exact h

theorem scale_identity (m : ℝ) (hm : m ≠ 0) (r k : ℕ) (hk : k ≤ r) :
    ((12:ℝ)/m)^(r+1) * m =
      (12:ℝ)^(k+1) * (1/m)^k * ((12:ℝ)/m)^(r-k) := by
  rw [show r+1 = (k+1)+(r-k) by omega, pow_add]
  rw [pow_succ, div_pow, one_div_pow]
  field_simp
  <;> ring

/-- Exact equality, not an asymptotic expansion: the normalized moment is a
polynomial evaluated at 1/M, for every positive integer M and every degree. -/
theorem normalizedEGFPolynomial_exact (M r : ℕ) (hM : M ≠ 0) :
    (normalizedEGFPolynomial r).eval (1/(M:ℝ)) =
      ((12:ℝ)/(M:ℝ))^r * PowerSeries.coeff r (evenEGF^M) := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [normalizedEGFPolynomial, PowerSeries.coeff_zero_eq_constantCoeff]
    | succ r =>
      rw [normalizedEGFPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      have hs :
          (∑ k ∈ range (r+1), (12:ℝ)^(k+1) * cumulantCoefficient k *
            (1/(M:ℝ))^k * (normalizedEGFPolynomial (r-k)).eval (1/(M:ℝ))) =
          ((12:ℝ)/(M:ℝ))^(r+1) * ((M:ℝ) * ∑ k ∈ range (r+1),
            cumulantCoefficient k * PowerSeries.coeff (r-k) (evenEGF^M)) := by
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkr : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [ih (r-k) (by omega), scale_identity _ hm r k hkr]
        ring
      rw [hs, ← power_coefficient_recurrence]
      have hr : (r+1:ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring

#print axioms normalizedEGFPolynomial_exact

#print axioms even_moment_coefficient
#print axioms cumulant_zero
#print axioms cumulant_one
end V033.UniformSum
