import Mathlib
import SpecialImaginaryPoint.EulerianAnalyticBracket
import SpecialImaginaryPoint.PeriodicOrbitAlgebraicity

/-!
# Eulerian–Parry transcendence: reduction to Hermite–Lindemann

The algebraic/analytic transfer is proved here *without* custom axioms.
The only remaining upstream deep-theorem prerequisite is a
kernel-checked Hermite–Lindemann assertion stating that the exponential
of the nonzero algebraic real 1/sqrt(2) is transcendental over Q.
No such result is assumed unconditionally in this file.
-/

namespace Manuscript14Section11

/-- The algebraic square-root factor at the Eulerian special point. -/
theorem eulerian_sqrt_two_algebraic :
    IsAlgebraic ℚ (Real.sqrt 2) := by
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  rw [hsq]
  exact isAlgebraic_natCast (R := ℚ) (A := ℝ) 2

/-- If exp(1/sqrt(2)) is transcendental, then so is the actual
Eulerian parameter sqrt(2)*sinh(1/sqrt(2)).
Only elementary algebraicity closure and the hyperbolic identity enter. -/
theorem eulerian_parameter_transcendental_of_exp
    (hexp : ¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2))) :
    ¬ IsAlgebraic ℚ eulerianParameter := by
  let a : ℝ := 1 / Real.sqrt 2
  let q : ℝ := Real.sqrt 2
  have hq : q ≠ 0 := by
    dsimp [q]
    positivity
  have hqalg : IsAlgebraic ℚ q := by
    simpa only [q] using eulerian_sqrt_two_algebraic
  intro hx
  have hx' : IsAlgebraic ℚ (q * Real.sinh a) := by
    simpa [eulerianParameter, q, a] using hx
  have hsinh : IsAlgebraic ℚ (Real.sinh a) := by
    have hm := hx'.mul hqalg.inv
    have heq : (q * Real.sinh a) * q⁻¹ = Real.sinh a := by
      field_simp [hq]
    rw [← heq]
    exact hm
  have hcosh2 : IsAlgebraic ℚ ((Real.cosh a) ^ 2) := by
    rw [Real.cosh_sq']
    exact (isAlgebraic_one (R := ℚ) (A := ℝ)).add (hsinh.pow 2)
  have hcosh : IsAlgebraic ℚ (Real.cosh a) :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) hcosh2
  have hrealexp : IsAlgebraic ℚ (Real.exp a) := by
    rw [← Real.sinh_add_cosh]
    exact hsinh.add hcosh
  exact hexp (by simpa only [a] using hrealexp)

/-- The genuine Eulerian greedy digits cannot be eventually periodic
provided the single deep Hermite–Lindemann exponential instance. -/
theorem eulerian_greedy_aperiodic_of_exp_transcendental
    (hexp : ¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2))) :
    ¬ ∃ m p : ℕ, 0 < p ∧
      ∀ n, m ≤ n →
        greedyDigit eulerianParameter (n + p) =
          greedyDigit eulerianParameter n := by
  have hbound : (1085441641272 : ℝ) / 10 ^ 12 <
      eulerianParameter := by
    simpa [eulerianParameter, eulerianParryValue] using
      eulerianParryValue_rational_bracket.1
  have hbeta : 1 < eulerianParameter := by linarith
  exact greedy_digits_not_eventually_periodic_of_transcendental
    eulerianParameter hbeta (eulerian_parameter_transcendental_of_exp hexp)

#print axioms Manuscript14Section11.eulerian_sqrt_two_algebraic
#print axioms Manuscript14Section11.eulerian_parameter_transcendental_of_exp
#print axioms Manuscript14Section11.eulerian_greedy_aperiodic_of_exp_transcendental

end Manuscript14Section11
