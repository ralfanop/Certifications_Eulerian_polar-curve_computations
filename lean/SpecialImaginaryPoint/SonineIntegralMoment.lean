import Mathlib
import SpecialImaginaryPoint.SonineRadialFormal

/-!
# Manuscript 14.1, §4: actual integral moments of the Sonine averaging operator

For each n : ℕ, define the *genuine real integral*

  Jₙ = (1/2) ∫ u in -1..1, (1-u²)^n.

The proof applies the fundamental theorem of calculus to the polynomial
u*(1-u²)^(n+1), whose endpoint values are zero. This yields the Sonine
recurrence and identifies the true integral with the previously certified
rational recurrence, for ALL n, not just sampled indices.

The extension from monomials to entire functions, and the analytic
interchange of differentiation and integration, remain separate obligations.
No additional axioms, sorries, or computed boolean axioms are admitted.
-/

namespace Manuscript14Sonine

open MeasureTheory intervalIntegral

noncomputable def integralMoment (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n

/-- The endpoint-vanishing polynomial identity, differentiated exactly. -/
private theorem hasDerivAt_momentPrimitive (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun u : ℝ => u * (1 - u ^ 2) ^ (n + 1))
      ((2 * (n : ℝ) + 3) * (1 - x ^ 2) ^ (n + 1) -
        (2 * (n : ℝ) + 2) * (1 - x ^ 2) ^ n) x := by
  have hbase : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)) using 1 <;> ring
  have hmul := (hasDerivAt_id x).mul (hbase.pow (n + 1))
  convert hmul using 1
  rw [pow_succ]
  push_cast
  ring

private theorem integralMoment_unscaled_recurrence (n : ℕ) :
    (2 * (n : ℝ) + 3) *
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (n + 1)) =
      (2 * (n : ℝ) + 2) *
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n) := by
  have hi (k : ℕ) :
      IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ k)
        volume (-1 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh :
      (∫ u in (-1 : ℝ)..1,
        ((2 * (n : ℝ) + 3) * (1 - u ^ 2) ^ (n + 1) -
          (2 * (n : ℝ) + 2) * (1 - u ^ 2) ^ n)) = 0 := by
    have hint :
        IntervalIntegrable
          (fun u : ℝ =>
            (2 * (n : ℝ) + 3) * (1 - u ^ 2) ^ (n + 1) -
              (2 * (n : ℝ) + 2) * (1 - u ^ 2) ^ n)
          volume (-1 : ℝ) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-1 : ℝ)) (b := (1 : ℝ))
      (f := fun u : ℝ => u * (1 - u ^ 2) ^ (n + 1))
      (f' := fun u : ℝ =>
        (2 * (n : ℝ) + 3) * (1 - u ^ 2) ^ (n + 1) -
          (2 * (n : ℝ) + 2) * (1 - u ^ 2) ^ n)
      (fun u _ => hasDerivAt_momentPrimitive n u) hint
    simpa using hftc
  rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hh
  · linarith
  · exact (hi (n + 1)).const_mul _
  · exact (hi n).const_mul _

theorem integralMoment_zero : integralMoment 0 = 1 := by
  norm_num [integralMoment, intervalIntegral.integral_const]

theorem integralMoment_recurrence (n : ℕ) :
    (2 * (n : ℝ) + 3) * integralMoment (n + 1) =
      (2 * (n : ℝ) + 2) * integralMoment n := by
  dsimp [integralMoment]
  linear_combination (1 / 2 : ℝ) * integralMoment_unscaled_recurrence n

/-- The integral coefficients equal the rational moments defined by recurrence. -/
theorem integralMoment_eq_moment (n : ℕ) :
    integralMoment n = (moment n : ℝ) := by
  induction n with
  | zero =>
      simpa [moment] using integralMoment_zero
  | succ n ih =>
      have h1 := integralMoment_recurrence n
      rw [ih] at h1
      have h2 :
          (2 * (n : ℝ) + 3) * (moment (n + 1) : ℝ) =
            (2 * (n : ℝ) + 2) * (moment n : ℝ) := by
        exact_mod_cast moment_recurrence n
      have hden : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      exact mul_left_cancel₀ hden (h1.trans h2.symm)

/-- Actual Sonine integral moment for the monomial u^(2n). -/
theorem integral_monomial_sonine (n : ℕ) :
    (1 / 2 : ℝ) * (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n) =
      (moment n : ℝ) := integralMoment_eq_moment n

#print axioms Manuscript14Sonine.integralMoment_zero
#print axioms Manuscript14Sonine.integralMoment_recurrence
#print axioms Manuscript14Sonine.integralMoment_eq_moment
#print axioms Manuscript14Sonine.integral_monomial_sonine

end Manuscript14Sonine
