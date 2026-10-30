import EulerianGrothendieck.UniformConvolutions
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Factorial.Basic

/-! Bounds on the actual logarithmic-derivative coefficients of the uniform
moment series. These are derived from the series identity, not assumed. -/
noncomputable section
open scoped BigOperators
open Finset Polynomial PowerSeries
namespace EulerianGrothendieck

def standardUniformCumulant (j : ℕ) : ℝ :=
  12^(j+1)*V033.UniformSum.cumulantCoefficient j

theorem uniformEGFCoefficient_scaled (k : ℕ) :
    uniformEGFCoefficient k = 12^k * PowerSeries.coeff k V033.UniformSum.evenEGF := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) k) uniformEGF_series
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale] using h

theorem uniformEGFCoefficient_zero : uniformEGFCoefficient 0 = 1 := by
  norm_num [uniformEGFCoefficient]

theorem uniformEGFCoefficient_le_one (j : ℕ) : uniformEGFCoefficient j ≤ 1 := by
  apply (uniformEGFCoefficient_le_gaussian j).trans
  unfold gaussianEGFCoefficient
  apply (div_le_one (by positivity)).2
  have hf : (1:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hp : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  nlinarith

theorem uniformEGF_derivative_coefficient_le_one (j : ℕ) :
    (j+1:ℝ)*uniformEGFCoefficient (j+1) ≤ 1 := by
  calc
    _ ≤ (j+1:ℝ)*gaussianEGFCoefficient (j+1) :=
      mul_le_mul_of_nonneg_left (uniformEGFCoefficient_le_gaussian _) (by positivity)
    _ = 1/(2^(j+1)*(j.factorial:ℝ)) := by
      unfold gaussianEGFCoefficient
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    _ ≤ 1 := by
      apply (div_le_one (by positivity)).2
      have hf : (1:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
      have hp : (1:ℝ) ≤ 2^(j+1) := one_le_pow₀ (by norm_num)
      nlinarith

theorem standardUniformCumulant_recurrence (n : ℕ) :
    standardUniformCumulant n +
      ∑ j ∈ range n, standardUniformCumulant j * uniformEGFCoefficient (n-j) =
      (n+1:ℝ)*uniformEGFCoefficient (n+1) := by
  have h := congrArg (PowerSeries.coeff (R := ℝ) n) V033.UniformSum.cumulant_identity
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j l => PowerSeries.coeff j V033.UniformSum.cumulantSeries *
        PowerSeries.coeff l V033.UniformSum.evenEGF) n,
    PowerSeries.coeff_derivative] at h
  have hscale := congrArg (fun x : ℝ => 12^(n+1)*x) h
  dsimp only at hscale
  rw [Finset.mul_sum] at hscale
  have heq : (∑ j ∈ range (n+1), standardUniformCumulant j*uniformEGFCoefficient (n-j)) =
      (n+1:ℝ)*uniformEGFCoefficient (n+1) := by
    rw [uniformEGFCoefficient_scaled]
    convert hscale using 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [standardUniformCumulant, uniformEGFCoefficient_scaled,
        V033.UniformSum.cumulantCoefficient]
      rw [show 12^(j+1)*PowerSeries.coeff j V033.UniformSum.cumulantSeries *
        (12^(n-j)*PowerSeries.coeff (n-j) V033.UniformSum.evenEGF) =
        (12^(j+1)*12^(n-j))*(PowerSeries.coeff j V033.UniformSum.cumulantSeries *
        PowerSeries.coeff (n-j) V033.UniformSum.evenEGF) by ring,
        ← pow_add, show j+1+(n-j)=n+1 by omega]
    · ring
  rw [Finset.sum_range_succ, Nat.sub_self, uniformEGFCoefficient_zero, mul_one] at heq
  linarith

theorem standardUniformCumulant_bound (n : ℕ) : |standardUniformCumulant n| ≤ 2^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have heq := standardUniformCumulant_recurrence n
    have habs : |standardUniformCumulant n| ≤
        1 + ∑ j ∈ range n, (2:ℝ)^j := by
      calc
        _ = |(n+1:ℝ)*uniformEGFCoefficient (n+1) -
          ∑ j ∈ range n, standardUniformCumulant j*uniformEGFCoefficient (n-j)| := by
          congr 1; linarith
        _ ≤ |(n+1:ℝ)*uniformEGFCoefficient (n+1)| +
          |∑ j ∈ range n, standardUniformCumulant j*uniformEGFCoefficient (n-j)| := abs_sub _ _
        _ ≤ 1 + ∑ j ∈ range n, |standardUniformCumulant j*uniformEGFCoefficient (n-j)| := by
          apply add_le_add
          · rw [abs_of_nonneg (mul_nonneg (by positivity) (uniformEGFCoefficient_nonneg _))]
            exact uniformEGF_derivative_coefficient_le_one n
          · exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ 1 + ∑ j ∈ range n, (2:ℝ)^j := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul, abs_of_nonneg (uniformEGFCoefficient_nonneg _)]
          exact (mul_le_mul_of_nonneg_right (ih j (Finset.mem_range.mp hj))
            (uniformEGFCoefficient_nonneg _)).trans
            (mul_le_of_le_one_right (by positivity) (uniformEGFCoefficient_le_one _))
    have hg := geom_sum_mul (2:ℝ) n
    norm_num at hg
    linarith

theorem standardUniformCumulant_zero : standardUniformCumulant 0 = 1/2 := by
  rw [standardUniformCumulant, V033.UniformSum.cumulant_zero]
  norm_num

theorem standardUniformCumulant_one : standardUniformCumulant 1 = -1/10 := by
  rw [standardUniformCumulant, V033.UniformSum.cumulant_one]
  norm_num

end EulerianGrothendieck
