import V033Core
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace V033
open intervalIntegral

theorem uniform_even_integral (r : ℕ) :
    (∫ x in (-1/2:ℝ)..(1/2:ℝ), x^(2*r)) =
      1 / ((4:ℝ)^r * (2*(r:ℝ)+1)) := by
  rw [integral_pow]
  have hn : (-1/2:ℝ) = -(1/2:ℝ) := by ring
  rw [hn, neg_pow, pow_add, pow_mul]
  norm_num
  simp only [← inv_pow]
  norm_num
  ring

theorem uniform_odd_integral (r : ℕ) :
    (∫ x in (-1/2:ℝ)..(1/2:ℝ), x^(2*r+1)) = 0 := by
  rw [integral_pow]
  have hn : (-1/2:ℝ) = -(1/2:ℝ) := by ring
  rw [hn, neg_pow]
  have hp : (-1:ℝ)^(2*r+1+1) = 1 := by
    rw [show 2*r+1+1=2*(r+1) by omega, pow_mul]
    norm_num
  rw [hp]
  ring

#print axioms uniform_even_integral
#print axioms uniform_odd_integral
end V033
