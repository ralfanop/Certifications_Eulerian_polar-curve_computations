import Mathlib

/-!
# Manuscript 14, Section 11 — rational Parry-threshold certificates

Kernel checks for rational polynomial signs and transport of inequalities.
The analytic identification with the Eulerian sinc/hyperbolic-sine value,
and the invariant-density theorem, remain separate proof obligations.
-/

namespace Manuscript14Section11

private def leftBracket : ℚ := 10854 / 10000
private def rightBracket : ℚ := 1085445 / 1000000

theorem f32_left_positive :
    (1 : ℚ) < leftBracket ^ 31 * (leftBracket - 1) := by
  norm_num [leftBracket]

theorem f31_right_negative :
    rightBracket ^ 30 * (rightBracket - 1) < (1 : ℚ) := by
  norm_num [rightBracket]

theorem delta_left_exact :
    (313240 : ℚ) / 10^9 <
      1 - (1085441641273 : ℚ) ^ 30 / (10^12)^30 *
            ((1085441641273 : ℚ) / 10^12 - 1) := by
  norm_num

theorem delta_right_exact :
    1 - (1085441641272 : ℚ) ^ 30 / (10^12)^30 *
            ((1085441641272 : ℚ) / 10^12 - 1) <
      (313241 : ℚ) / 10^9 := by
  norm_num

theorem strict_parry_return (x : ℝ)
    (hx_lower : (10854 : ℝ) / 10000 < x)
    (hx_upper : x < (1085445 : ℝ) / 1000000) :
    1 < x ^ 31 * (x - 1) ∧ x ^ 30 * (x - 1) < 1 := by
  have hp : (0 : ℝ) ≤ x := by
    linarith
  have hlo : (1 : ℝ) <
      ((10854 : ℝ) / 10000)^31 * ((10854 : ℝ) / 10000 - 1) := by
    norm_num
  have hhi : ((1085445 : ℝ) / 1000000)^30 *
        ((1085445 : ℝ) / 1000000 - 1) < 1 := by
    norm_num
  constructor
  · have hpow : ((10854 : ℝ) / 10000)^31 ≤ x^31 := by
      gcongr
    have hmul : ((10854 : ℝ) / 10000)^31 *
        ((10854 : ℝ) / 10000 - 1) ≤ x^31 * (x-1) := by
      calc
        _ ≤ x^31 * ((10854 : ℝ) / 10000 - 1) :=
          mul_le_mul_of_nonneg_right hpow (by norm_num)
        _ ≤ x^31 * (x - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have hpow : x^30 ≤ ((1085445 : ℝ) / 1000000)^30 := by
      gcongr
    have hpos : (0 : ℝ) ≤ x - 1 := by
      linarith
    have hmul : x^30 * (x-1) ≤
        ((1085445 : ℝ) / 1000000)^30 *
        ((1085445 : ℝ) / 1000000 - 1) := by
      calc
        _ ≤ ((1085445 : ℝ) / 1000000)^30 * (x - 1) :=
          mul_le_mul_of_nonneg_right hpow hpos
        _ ≤ ((1085445 : ℝ) / 1000000)^30 *
            ((1085445 : ℝ) / 1000000 - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

#print axioms Manuscript14Section11.f32_left_positive
#print axioms Manuscript14Section11.f31_right_negative
#print axioms Manuscript14Section11.delta_left_exact
#print axioms Manuscript14Section11.delta_right_exact
#print axioms Manuscript14Section11.strict_parry_return

end Manuscript14Section11
