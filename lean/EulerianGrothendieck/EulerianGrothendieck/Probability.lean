import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
namespace EulerianGrothendieck

def uniformMoment (n : ℕ) : ℝ := ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), x ^ n

theorem uniform_second_moment : uniformMoment 2 = 1 / 12 := by
  unfold uniformMoment
  rw [integral_pow]
  norm_num

theorem uniform_fourth_moment : uniformMoment 4 = 1 / 80 := by
  unfold uniformMoment
  rw [integral_pow]
  norm_num

theorem uniform_fourth_cumulant :
    uniformMoment 4 - 3 * (uniformMoment 2) ^ 2 = -(1 / 120 : ℝ) := by
  rw [uniform_second_moment, uniform_fourth_moment]
  norm_num

theorem standardized_fourth_cumulant :
    (uniformMoment 4 - 3 * (uniformMoment 2) ^ 2) / (uniformMoment 2) ^ 2 =
      -(6 / 5 : ℝ) := by
  rw [uniform_fourth_cumulant, uniform_second_moment]
  norm_num

theorem edgeworth_density_coefficient : (-(6 / 5 : ℝ)) / 24 = -(1 / 20 : ℝ) := by
  norm_num

/-- Algebraic fourth-moment/Jacobi relation, not a probability-law identification. -/
theorem jacobi_fourth_cumulant_identity (b₁ b₂ : ℝ) :
    (b₁ ^ 2 + b₁ * b₂) - 3 * b₁ ^ 2 = b₁ * (b₂ - 2 * b₁) := by ring

theorem uniform_jacobi_cumulant_polynomial (M : ℝ) :
    (M / 12) * ((M / 6 - 1 / 10) - 2 * (M / 12)) = -M / 120 := by ring

/-- Exact one-variable Gaussian-normalized moment factors. -/
def momentFactor : ℕ → ℝ
  | 0 => 1
  | n + 1 => momentFactor n * (3 / (2 * (n : ℝ) + 3))

theorem momentFactor_nonneg (n : ℕ) : 0 ≤ momentFactor n := by
  induction n with
  | zero => norm_num [momentFactor]
  | succ n ih => simp only [momentFactor]; positivity

theorem momentFactor_le_one (n : ℕ) : momentFactor n ≤ 1 := by
  induction n with
  | zero => norm_num [momentFactor]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd : (0 : ℝ) < 2 * n + 3 := by positivity
    have hf : (3 : ℝ) / (2 * n + 3) ≤ 1 := (div_le_one hd).2 (by linarith)
    calc
      momentFactor (n + 1) = momentFactor n * (3 / (2 * (n : ℝ) + 3)) := rfl
      _ ≤ 1 * (3 / (2 * (n : ℝ) + 3)) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ 1 := by simpa using hf

theorem momentFactor_two : momentFactor 2 = (3 / 5 : ℝ) := by
  norm_num [momentFactor]
theorem uniform_even_moment (k : ℕ) :
    uniformMoment (2*k) = 1 / ((2 : ℝ)^(2*k) * (2*(k : ℝ)+1)) := by
  unfold uniformMoment
  rw [integral_pow]
  have ho : Odd (2*k+1) := ⟨k, rfl⟩
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, ho.neg_pow]
  simp only [div_pow, one_pow, pow_succ]
  push_cast
  field_simp
  <;> ring

theorem uniform_odd_moment (k : ℕ) : uniformMoment (2*k+1) = 0 := by
  unfold uniformMoment
  rw [integral_pow]
  have he : Even (2*k+1+1) := ⟨k+1, by omega⟩
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, he.neg_pow]
  simp

end EulerianGrothendieck

