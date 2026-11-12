import Manuscript15.UniformAllOrderMomentBridge

/-!
# Manuscript 15 — positivity and quantitative bounds for genuine moments

Every statement concerns actual Lebesgue moments of the centered
uniform Borel probability law, not a formal generating series.
The all-order exact integral formulas are imported from the
kernel-certified measure-level moment bridge.
-/

noncomputable section
namespace Manuscript15

open MeasureTheory Real

/-- Every even moment of the genuine centered uniform probability
    measure is strictly positive. -/
theorem centredUniformLaw_even_moment_pos (n : ℕ) :
    0 < (∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) := by
  rw [centredUniformLaw_even_moment_all]
  positivity

/-- All even moments are bounded by the n-th power of 1/4,
    with no asymptotic or floating-point estimates. -/
theorem centredUniformLaw_even_moment_le_quarter_pow (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) ≤
      1 / (4 : ℝ) ^ n := by
  rw [centredUniformLaw_even_moment_all]
  have hden : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hfactor : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) <
    ((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n) hden).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) (le_of_lt hden)]

/-- At every strictly positive even degree the moment is less than one. -/
theorem centredUniformLaw_even_moment_lt_one (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) < 1 := by
  rw [centredUniformLaw_even_moment_all]
  have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num) 
  have hfactor : (1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * n + 1 by omega)
  have hden : (1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n := by
    nlinarith
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) <
    ((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n)).2 (by nlinarith)

#print axioms Manuscript15.centredUniformLaw_even_moment_pos
#print axioms Manuscript15.centredUniformLaw_even_moment_le_quarter_pow
#print axioms Manuscript15.centredUniformLaw_even_moment_lt_one
end Manuscript15
