import Manuscript15.UniformEulerianCharacteristicMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Manuscript 15 — exact ALL-ORDER moments of the genuine Eulerian interval measure

The actual Borel probability measure μ_E = volume.restrict [-1/2,1/2]
has characteristic function rE(t) = sinc(t/2).

This module computes its moments, not by a truncated Taylor series,
but from genuine Lebesgue integrals at EVERY order n:

  ∫ x^2n dμ_E = 1/((2n+1)*4^n),
  ∫ x^(2n+1) dμ_E = 0.

In addition, the even moment divided by (2n)! is the exact positive
factorial quantity 1/((2n+1)!*4^n). Thus the alternating Taylor
coefficients associated with the characteristic function have the
expected formula (-1)^n /((2n+1)!*4^n).

These classical moment identities are a separate analytic bridge
between actual probability measures and the formal coefficients in
Manuscript 15. This module does not *yet* prove that these numbers
satisfy the nonlinear two-scale coefficient recurrence.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Real Set intervalIntegral
open scoped Real

/-- Exact integral of an arbitrary even power over the unit-length
symmetric interval. The integrand and interval are genuine real. -/
theorem centeredUniform_interval_even_power_integral (n : ℕ) :
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

/-- Every odd monomial integrates to zero over the symmetric
unit-length interval, with no asymptotic or parity approximation. -/
theorem centeredUniform_interval_odd_power_integral (n : ℕ) :
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

/-- All even moments of the ACTUAL centered uniform probability
measure are exact factorial-independent rational real quantities. -/
theorem eulerianUniformMeasure_evenMoment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂eulerianUniformMeasure) =
      1 / (((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  calc
    (∫ x : ℝ, x ^ (2 * n) ∂eulerianUniformMeasure) =
        ∫ x in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
          x ^ (2 * n) ∂volume := by
      simp [eulerianUniformMeasure]
    _ = ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          x ^ (2 * n) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
    _ = 1 / (((2 * n + 1 : ℕ) : ℝ) * (4 : ℝ) ^ n) :=
      centeredUniform_interval_even_power_integral n

/-- Every odd moment of the ACTUAL centered uniform probability
measure vanishes exactly, at every index. -/
theorem eulerianUniformMeasure_oddMoment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂eulerianUniformMeasure) = 0 := by
  calc
    (∫ x : ℝ, x ^ (2 * n + 1) ∂eulerianUniformMeasure) =
        ∫ x in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
          x ^ (2 * n + 1) ∂volume := by
      simp [eulerianUniformMeasure]
    _ = ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          x ^ (2 * n + 1) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
    _ = 0 := centeredUniform_interval_odd_power_integral n


/-- Exact factorial-normalized moment of the ACTUAL centered interval
measure: at every n, the (2n)-th moment divided by (2n)! equals
1/((2n+1)! 4^n), matching the positive sinc coefficient magnitude. -/
theorem eulerianUniformMeasure_evenMoment_factorial (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂eulerianUniformMeasure) /
      (((2 * n).factorial : ℕ) : ℝ) =
        1 / ((((2 * n + 1).factorial : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  have hfac :
      ((((2 * n + 1).factorial : ℕ) : ℝ)) =
        (((2 * n + 1 : ℕ) : ℝ)) *
          ((((2 * n).factorial : ℕ) : ℝ)) := by
    rw [Nat.factorial_succ]
    norm_cast
  rw [eulerianUniformMeasure_evenMoment, hfac]
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

/-- The exact signed even-order Fourier–Taylor coefficient derived
from the actual centered uniform probability measure at EVERY n,
without inferring the coefficient from finitely many numerical terms. -/
theorem eulerianUniformMeasure_evenTaylorMomentCoefficient (n : ℕ) :
    (-1 : ℝ) ^ n *
      ((∫ x : ℝ, x ^ (2 * n) ∂eulerianUniformMeasure) /
        (((2 * n).factorial : ℕ) : ℝ)) =
      (-1 : ℝ) ^ n /
        ((((2 * n + 1).factorial : ℕ) : ℝ) * (4 : ℝ) ^ n) := by
  have h := eulerianUniformMeasure_evenMoment_factorial n
  simpa [div_eq_mul_inv, mul_assoc] using
    congrArg (fun y : ℝ => (-1 : ℝ) ^ n * y) h

#print axioms Manuscript15.centeredUniform_interval_even_power_integral
#print axioms Manuscript15.centeredUniform_interval_odd_power_integral
#print axioms Manuscript15.eulerianUniformMeasure_evenMoment
#print axioms Manuscript15.eulerianUniformMeasure_oddMoment
#print axioms Manuscript15.eulerianUniformMeasure_evenMoment_factorial
#print axioms Manuscript15.eulerianUniformMeasure_evenTaylorMomentCoefficient

end Manuscript15
