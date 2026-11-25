import Manuscript15.CrossQuarticPeriodDifferential20261125
import Mathlib

/-!
# M15 25 Nov 2026: finite-interval elliptic period substitution

Authoritative source: M15 Proposition 10.2, Eq. (555)
in Manuscript_15_20261125_CROSS_CONNECTIONS(1).zip.

This module establishes the actual integral change of variables on
EVERY finite interval [0,r], 0 ≤ r < 1, for the exact real elliptic
integrands. It invokes Mathlib's genuine intervalIntegral change of
variables theorem, with continuous real map, its actual HasDerivAt,
and positive derivative independently established.

It is not the full improper integral identity at r → 1,
which additionally requires convergence and a limit theorem.
The source genus-one projective morphism is also separate.
-/

namespace Manuscript15.CrossQuarticFinitePeriod20261125

open Manuscript15.CrossQuartic20261125
open Manuscript15.CrossQuarticPeriodDifferential20261125
open scoped Interval

/-- Target elliptic period integrand on the positive real branch. -/
noncomputable def targetIntegrand (z : ℝ) : ℝ :=
  1 / Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2))

/-- Source elliptic period integrand after the degree-two map. -/
noncomputable def sourceIntegrand (t : ℝ) : ℝ :=
  Real.sqrt 2 / Real.sqrt (1 + t ^ 4)

/-- Explicit actual derivative dz/dt used in the substitution. -/
noncomputable def zDerivativeFormula (t : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + t ^ 2) / (1 - t ^ 2) ^ 2

/-- Strictly inside the regular chart, for any real t in [0,r]
with r<1, there is no pole at t=±1. -/
theorem period_chart_denominator (r t : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : t ∈ Set.uIcc 0 r) :
    1 - t ^ 2 ≠ 0 := by
  rw [Set.uIcc_of_le hr0] at ht
  have hlt : t < 1 := lt_of_le_of_lt ht.2 hr1
  have hbound : t ^ 2 < 1 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hlt.le)]
  exact ne_of_gt (by linarith)

/-- The actual rational quartic coordinate is continuous on
every real compact interval [0,r] strictly before the pole. -/
theorem quarticZ_continuousOn_uIcc (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn quarticZ (Set.uIcc 0 r) := by
  intro t ht
  exact ((quarticZ_hasDerivAt t
    (period_chart_denominator r t hr0 hr1 ht)).continuousAt).continuousWithinAt

/-- The genuine derivative formula holds at every point of the
interior of the finite integration interval. -/
theorem period_derivative_inside (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ t ∈ Set.Ioo (min (0 : ℝ) r) (max 0 r),
      HasDerivAt quarticZ (zDerivativeFormula t) t := by
  intro t ht
  have hinside : t ∈ Set.uIcc 0 r := by
    simp only [min_eq_left hr0, max_eq_right hr0] at ht
    rw [Set.uIcc_of_le hr0]
    exact ⟨ht.1.le, ht.2.le⟩
  simpa only [zDerivativeFormula] using
    quarticZ_hasDerivAt t (period_chart_denominator r t hr0 hr1 hinside)

/-- On the full regular domain the real derivative of z(t)
is nonnegative; the nonnegative-derivative integral substitution
can therefore be applied without an injectivity assumption. -/
theorem period_zDerivative_nonneg (t : ℝ) :
    0 ≤ zDerivativeFormula t := by
  unfold zDerivativeFormula
  positivity

/-- Pointwise identity of the actual integration density after
the substitution, with the derivative (not just a formal
differential notation) present as a multiplicative factor. -/
theorem period_integrands_equal_on_chart (t : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) :
    (targetIntegrand ∘ quarticZ) t * zDerivativeFormula t =
      sourceIntegrand t := by
  have h := actual_positive_period_integrand t ht
  rw [(quarticZ_hasDerivAt t ht).deriv] at h
  simpa only [targetIntegrand, sourceIntegrand, zDerivativeFormula,
    Function.comp_apply, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The actual finite-interval elliptic PERIOD identity.
For every 0 ≤ r < 1, the source integral from 0 to r
equals the target integral from 0 to z(r), by Mathlib's
analytical substitution theorem. This is a substantial
strict subgoal of the improper-integral Eq. (555). -/
theorem finite_elliptic_period_change_of_variables
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ z in (0 : ℝ)..quarticZ r, targetIntegrand z) =
      ∫ t in (0 : ℝ)..r, sourceIntegrand t := by
  have hcont := quarticZ_continuousOn_uIcc r hr0 hr1
  have hder := period_derivative_inside r hr0 hr1
  have hpos :
      ∀ t ∈ Set.Ioo (min (0 : ℝ) r) (max 0 r),
        0 ≤ zDerivativeFormula t := by
    intro t ht
    exact period_zDerivative_nonneg t
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := r) (f := quarticZ)
    (f' := zDerivativeFormula) (g := targetIntegrand)
    hcont hder hpos
  have hz0 : quarticZ 0 = 0 := by
    simp [quarticZ]
  rw [hz0] at hsub
  calc
    (∫ z in (0 : ℝ)..quarticZ r, targetIntegrand z) =
        ∫ t in (0 : ℝ)..r,
          (targetIntegrand ∘ quarticZ) t * zDerivativeFormula t := hsub.symm
    _ = ∫ t in (0 : ℝ)..r, sourceIntegrand t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact period_integrands_equal_on_chart t
        (period_chart_denominator r t hr0 hr1 ht)

#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.period_chart_denominator
#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.quarticZ_continuousOn_uIcc
#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.period_derivative_inside
#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.period_zDerivative_nonneg
#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.period_integrands_equal_on_chart
#print axioms Manuscript15.CrossQuarticFinitePeriod20261125.finite_elliptic_period_change_of_variables

end Manuscript15.CrossQuarticFinitePeriod20261125
