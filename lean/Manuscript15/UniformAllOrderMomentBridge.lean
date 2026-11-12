import Manuscript15.UniformCumulantInvariants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Manuscript 15 — all-order moments of the normalized conditional uniform law

The exact measure `centredUniformLaw` is the conditional Lebesgue measure
of Icc (-1/2) (1/2), constructed and certified in the preceding probability
module. This extends its individually verified moments of degrees 1,2,3,4,6
to EVERY natural order using genuine measure integrals, not an inference
from a finite sequence.

A separate formalization `EulerianUniformMoments` on another branch uses
a restricted measure; this module applies directly to `centredUniformLaw`,
which is the law in the measure-level cosine and sine characterizations.
It does not assume any analytic Taylor coefficient extraction theorem.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Real Set intervalIntegral
open scoped Real

/-- The oriented interval integral of every even power is exact. -/
private theorem centredUniformLaw_even_interval (n : ℕ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), x ^ (2 * n)) =
      1 / (((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  rw [integral_pow]
  have hneg :
      (-1 / 2 : ℝ) ^ (2 * n + 1) =
        -((1 / 2 : ℝ) ^ (2 * n + 1)) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, neg_pow]
    norm_num [pow_add, pow_mul]
  rw [hneg]
  have hfrac :
      (1 / 2 : ℝ) ^ (2 * n + 1) =
        1 / (2 * (4 : ℝ) ^ n) := by
    rw [pow_add, pow_mul]
    norm_num [div_pow, pow_two]
  rw [hfrac]
  have hden : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Every odd power integrates to zero over the centered interval. -/
private theorem centredUniformLaw_odd_interval (n : ℕ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), x ^ (2 * n + 1)) = 0 := by
  rw [integral_pow]
  have hEven : Even (2 * n + 1 + 1) := by
    refine ⟨n + 1, ?_⟩
    omega
  have hneg :
      (-1 / 2 : ℝ) ^ (2 * n + 1 + 1) =
        (1 / 2 : ℝ) ^ (2 * n + 1 + 1) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, hEven.neg_pow]
  rw [hneg]
  simp

/-- All even raw moments of the actual Borel probability law. -/
theorem centredUniformLaw_even_moment_all (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) =
      1 / (((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  rw [centredUniformLaw_interval_integral]
  exact centredUniformLaw_even_interval n

/-- Vanishing of every odd raw moment of the actual probability law. -/
theorem centredUniformLaw_odd_moment_all (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂centredUniformLaw) = 0 := by
  rw [centredUniformLaw_interval_integral]
  exact centredUniformLaw_odd_interval n

/-- Exact factorial normalization of every even moment, not a
    finite-truncation identification. -/
theorem centredUniformLaw_even_moment_factorial_all (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) /
      (((2 * n).factorial : ℕ) : ℝ) =
        1 / ((((2 * n + 1).factorial : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  have hfac :
      ((((2 * n + 1).factorial : ℕ) : ℝ)) =
        (((2 * n + 1 : ℕ) : ℝ)) *
          ((((2 * n).factorial : ℕ) : ℝ)) := by
    rw [Nat.factorial_succ]
    norm_cast
  rw [centredUniformLaw_even_moment_all, hfac]
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

/-- The algebraic signed coefficient associated with each even moment
    is exactly the expected sinc coefficient. This is not by itself a
    Taylor expansion theorem for the analytic characteristic function. -/
theorem centredUniformLaw_even_signed_coefficient_all (n : ℕ) :
    (-1 : ℝ) ^ n *
      ((∫ x : ℝ, x ^ (2 * n) ∂centredUniformLaw) /
        (((2 * n).factorial : ℕ) : ℝ)) =
      (-1 : ℝ) ^ n /
        ((((2 * n + 1).factorial : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  have h := centredUniformLaw_even_moment_factorial_all n
  simpa [div_eq_mul_inv, mul_assoc] using
    congrArg (fun y : ℝ => (-1 : ℝ) ^ n * y) h

#print axioms Manuscript15.centredUniformLaw_even_moment_all
#print axioms Manuscript15.centredUniformLaw_odd_moment_all
#print axioms Manuscript15.centredUniformLaw_even_moment_factorial_all
#print axioms Manuscript15.centredUniformLaw_even_signed_coefficient_all

end Manuscript15
