import Manuscript15.CoefficientRigidity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Manuscript 15 — coefficient extraction from a genuine formal power-series identity

Let G(u)=Σ c_n u^n denote a FORMAL power series over ℝ, and consider
  1 - G(4u) - 2u (d/du)[G(4u)] = (u/2) G(u)^2.

In PowerSeries notation, G(4u) is the EXACT rescale 4 G, and the
formal derivative is Mathlib's PowerSeries.derivative. This identity
is the squared-variable (u=t²) version of the two-scale cycloidal
equation for an even generating function f(t)=G(t²).

By extracting the constant coefficient and each coefficient u^(n+1),
we derive EXACTLY the existing Manuscript15.CoefficientRule c:

  c₀ = 1,
  (2n+3) 4^(n+1) c_(n+1)
    = -(1/2) Σ_{j=0}^n c_j c_(n-j).

This proves a substantive FORMAL-SERIES extraction obligation.
It does not yet claim that the original analytic functional equation
implies the formal identity, nor that a characteristic function
realizes it; analytic convergence remains a separate obligation.
-/

noncomputable section

namespace Manuscript15

open PowerSeries
open scoped PowerSeries

/-- The exact formal-power-series two-scale cycloidal equation
expressed in the squared variable u=t², with no analytic convergence
assumption or truncated Taylor approximation. -/
def FormalTwoScaleEquation (c : ℕ → ℝ) : Prop :=
  let G : PowerSeries ℝ := PowerSeries.mk c
  (1 : PowerSeries ℝ) - PowerSeries.rescale (4 : ℝ) G -
    (2 : ℝ) • ((PowerSeries.X : PowerSeries ℝ) *
      PowerSeries.derivative (PowerSeries.rescale (4 : ℝ) G)) =
    (1 / 2 : ℝ) • ((PowerSeries.X : PowerSeries ℝ) * (G * G))

/-- Exact coefficient extraction from the FORMAL two-scale cycloidal
differential equation implies the independently formalized conditional
rigidity recurrence, including c₀=1 and every n≥0 coefficient rule.
No use of unproved analytic convergence is made. -/
theorem formalTwoScaleEquation_implies_coefficientRule
    (c : ℕ → ℝ) (h : FormalTwoScaleEquation c) :
    CoefficientRule c := by
  dsimp [FormalTwoScaleEquation] at h
  constructor
  · have h0 :=
      congrArg (PowerSeries.coeff (R := ℝ) 0) h
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_mk] at h0
    linarith
  · intro n
    have hraw :
        -((4 : ℝ) ^ (n + 1) * c (n + 1)) -
          2 * (((4 : ℝ) ^ (n + 1) * c (n + 1)) * (n + 1 : ℝ)) =
            (1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (n + 1), c j * c (n - j) := by
      simpa [PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
        PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
          (congrArg (PowerSeries.coeff (R := ℝ) (n + 1)) h)
    calc
      (((2 * (n + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1)) * c (n + 1) =
          -(-((4 : ℝ) ^ (n + 1) * c (n + 1)) -
            2 * (((4 : ℝ) ^ (n + 1) * c (n + 1)) * (n + 1 : ℝ))) := by
              push_cast
              ring
      _ = -((1 / 2 : ℝ) *
            ∑ j ∈ Finset.range (n + 1), c j * c (n - j)) := by
              rw [hraw]

#print axioms Manuscript15.formalTwoScaleEquation_implies_coefficientRule

end Manuscript15
