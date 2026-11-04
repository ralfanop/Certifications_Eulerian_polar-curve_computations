import Mathlib
import SpecialImaginaryPoint.UpstreamLindemannBasic
import SpecialImaginaryPoint.EulerianTranscendenceReduction

/-!
# Manuscript 14.10 — Unconditional Hermite–Lindemann Eulerian endpoint

The deep Hermite–Lindemann theorem comes from Yuyang Zhao's Apache-2.0
formalization in Mathlib PR #28013, backported to this branch as an
explicit, independently kernel-checked dependency.
This file contains NO additional axioms and NO `sorry`.
-/

namespace Manuscript14Section11

/-- The nonzero algebraic Eulerian exponent is algebraic over the integers
after passage to the complex numbers. -/
theorem eulerian_complex_exponent_algebraic_integer :
    IsAlgebraic ℤ (((1 / Real.sqrt 2 : ℝ) : ℂ)) := by
  have hq :
      IsAlgebraic ℚ (((1 / Real.sqrt 2 : ℝ) : ℂ)) := by
    simpa only using
      (eulerian_exponent_algebraic_nonzero.1.algebraMap (A := ℂ))
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hq

/-- Hermite–Lindemann at the actual Eulerian special exponent, not a
hypothesis about the exponential value. -/
theorem eulerian_exponential_transcendental :
    ¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2)) := by
  let a : ℝ := 1 / Real.sqrt 2
  have ha0 : ((a : ℂ)) ≠ 0 := by
    exact_mod_cast eulerian_exponent_algebraic_nonzero.2
  have haz : IsAlgebraic ℤ (a : ℂ) := by
    simpa only [a] using eulerian_complex_exponent_algebraic_integer
  have ht : Transcendental ℤ (Complex.exp (a : ℂ)) :=
    transcendental_exp ha0 haz
  intro hr
  have hq : IsAlgebraic ℚ (Complex.exp (a : ℂ)) := by
    have hc : IsAlgebraic ℚ
        (((Real.exp (1 / Real.sqrt 2)) : ℝ) : ℂ) := by
      simpa only using (hr.algebraMap (A := ℂ))
    simpa only [a, Complex.ofReal_exp] using hc
  exact ht ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hq)

/-- Theorem 11.1, integrated: genuinely unconditional dynamical,
transcendence and nonperiodicity conclusions at the Eulerian special point. -/
theorem eulerian_parry_section11_unconditional :
    ((greedyDigit eulerianParameter 0 = 1 ∧
      (∀ k : ℕ, k < 30 → greedyDigit eulerianParameter (k + 1) = 0) ∧
      greedyDigit eulerianParameter 31 = 1) ∧
    ((313240 : ℝ) / 10 ^ 9 <
      1 - (greedyMap eulerianParameter)^[31] 1 ∧
      1 - (greedyMap eulerianParameter)^[31] 1 <
        (313241 : ℝ) / 10 ^ 9) ∧
    (∃ beta32 beta31 : ℝ,
      (1 < beta32 ∧ beta32 < 2 ∧ beta32 ^ 32 - beta32 ^ 31 - 1 = 0) ∧
      (1 < beta31 ∧ beta31 < 2 ∧ beta31 ^ 31 - beta31 ^ 30 - 1 = 0) ∧
      beta32 < eulerianParameter ∧ eulerianParameter < beta31 ∧
      (greedyMap beta31)^[31] 1 = 0 ∧
      Filter.Tendsto (fun beta : ℝ => (greedyMap beta)^[31] 1)
        (𝓝[<] beta31) (𝓝 (1 : ℝ)))) ∧
    (¬ IsAlgebraic ℚ eulerianParameter) ∧
    (¬ ∃ m p : ℕ, 0 < p ∧
        ∀ n, m ≤ n →
          greedyDigit eulerianParameter (n + p) =
            greedyDigit eulerianParameter n) := by
  exact ⟨eulerian_parry_dynamical_part_unconditional,
    eulerian_parameter_transcendental_of_exp eulerian_exponential_transcendental,
    eulerian_greedy_aperiodic_of_exp_transcendental eulerian_exponential_transcendental⟩

#print axioms Manuscript14Section11.eulerian_complex_exponent_algebraic_integer
#print axioms Manuscript14Section11.eulerian_exponential_transcendental
#print axioms Manuscript14Section11.eulerian_parry_section11_unconditional

end Manuscript14Section11
