import Manuscript15.CanonicalFormalTwoScaleBridge
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Manuscript 15 — formal existence and uniqueness of the exact two-scale cycloidal solution

This module closes a central PURELY FORMAL-ALGEBRAIC proof obligation.
The exact coefficient recurrence is EQUIVALENT to the genuine Mathlib
PowerSeries differential equation

    1 - G(4u) - 2u (d/du)[G(4u)] = (u/2) G(u)^2,
    G(u) = Σ_{n≥0} c_n u^n.

The forward implication was independently kernel-certified. Here we
prove the REVERSE implication by coefficientwise PowerSeries equality,
using the exact rescale/derivative/shift/convolution identities.

The canonical all-order recurrence sequence therefore determines an
ACTUAL FORMAL power-series solution, and formal uniqueness gives
existence and uniqueness at the purely formal level.

No analytic convergence, entire-function existence, Fourier-profile
identification or probability-measure uniqueness is inferred.
-/

noncomputable section

namespace Manuscript15

open PowerSeries
open scoped PowerSeries

/-- The algebraic triangular two-scale recurrence implies the
FULL formal PowerSeries differential equation, without truncation. -/
theorem coefficientRule_implies_formalTwoScaleEquation
    (c : ℕ → ℝ) (hc : CoefficientRule c) :
    FormalTwoScaleEquation c := by
  dsimp [FormalTwoScaleEquation]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      have hCC :
          PowerSeries.constantCoeff
            (PowerSeries.rescale (4 : ℝ) (PowerSeries.mk c)) = c 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simp
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hCC, hc.1]
  | succ k =>
      have hL :
          PowerSeries.coeff (k + 1)
            ((PowerSeries.X : PowerSeries ℝ) *
              PowerSeries.derivative
                (PowerSeries.rescale (4 : ℝ) (PowerSeries.mk c))) =
            ((4 : ℝ) ^ (k + 1) * c (k + 1)) * (k + 1 : ℝ) := by
        rw [PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative,
          PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
      have hR :
          PowerSeries.coeff (k + 1)
            ((PowerSeries.X : PowerSeries ℝ) *
              (PowerSeries.mk c * PowerSeries.mk c)) =
            ∑ j ∈ Finset.range (k + 1), c j * c (k - j) := by
        rw [PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [PowerSeries.coeff_mk]
      have hrec := hc.2 k
      have hraw :
          -((4 : ℝ) ^ (k + 1) * c (k + 1)) -
            2 * (((4 : ℝ) ^ (k + 1) * c (k + 1)) * (k + 1 : ℝ)) =
              (1 / 2 : ℝ) *
                ∑ j ∈ Finset.range (k + 1), c j * c (k - j) := by
        push_cast at hrec
        linear_combination (-1) * hrec
      simpa [hL, hR, PowerSeries.coeff_rescale,
        PowerSeries.coeff_mk] using hraw

/-- The exact formal PowerSeries two-scale differential equation
and its triangular coefficient rule are logically EQUIVALENT. -/
theorem formalTwoScaleEquation_iff_coefficientRule (c : ℕ → ℝ) :
    FormalTwoScaleEquation c ↔ CoefficientRule c :=
  ⟨formalTwoScaleEquation_implies_coefficientRule c,
    coefficientRule_implies_formalTwoScaleEquation c⟩

/-- The uniquely defined canonical all-order algebraic coefficient
sequence is an ACTUAL formal solution of the exact two-scale equation. -/
theorem rigidityCoefficientSequence_formalTwoScaleEquation :
    FormalTwoScaleEquation rigidityCoefficientSequence :=
  coefficientRule_implies_formalTwoScaleEquation
    rigidityCoefficientSequence rigidityCoefficientSequence_rule

/-- There is exactly ONE real coefficient sequence whose
genuine formal PowerSeries satisfies the cycloidal two-scale
functional differential equation. -/
theorem formalTwoScaleEquation_existsUnique :
    ∃! c : ℕ → ℝ, FormalTwoScaleEquation c := by
  refine ⟨rigidityCoefficientSequence,
    rigidityCoefficientSequence_formalTwoScaleEquation, ?_⟩
  intro c hc
  exact formalTwoScaleEquation_eq_canonical c hc

#print axioms Manuscript15.coefficientRule_implies_formalTwoScaleEquation
#print axioms Manuscript15.formalTwoScaleEquation_iff_coefficientRule
#print axioms Manuscript15.rigidityCoefficientSequence_formalTwoScaleEquation
#print axioms Manuscript15.formalTwoScaleEquation_existsUnique

end Manuscript15
