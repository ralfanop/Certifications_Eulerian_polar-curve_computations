import Manuscript15.CrossQuarticCurve20261125
import Mathlib

/-!
# M15 (25 Nov 2026): the actual positive-branch elliptic differential

Source: Proposition 10.2 and eq:cross-curvePeriod15
of Manuscript_15_20261125_CROSS_CONNECTIONS(1).zip.

The original map's derivative identity dz/W = sqrt(2) dt/Y was
certified as a real derivative quotient in the previous module.

Here we establish the positive real square-root branches and
translate that differential into the ACTUAL analytic integrands
1/sqrt((1+z²)(1+2z²)) and sqrt(2)/sqrt(1+t⁴).
The pointwise identity holds for every real t with t² ≠ 1,
which is stronger than the interval 0<t<1 required by the
period integral.

DO NOT confuse this pointwise analytic identity with the
global improper integration claim. Change of variables
for interval and improper integrals remains to be certified.
-/

namespace Manuscript15.CrossQuarticPeriodDifferential20261125

open Manuscript15.CrossQuartic20261125

/-- The positive real branch of the source elliptic quartic. -/
noncomputable def positiveSourceY (t : ℝ) : ℝ :=
  Real.sqrt (1 + t ^ 4)

/-- The chosen real source branch satisfies the TRUE
source algebraic curve equation at every real t. -/
theorem positiveSourceY_sq (t : ℝ) :
    positiveSourceY t ^ 2 = 1 + t ^ 4 := by
  unfold positiveSourceY
  exact Real.sq_sqrt (by positivity)

/-- The positive real branch has no zeros. -/
theorem positiveSourceY_pos (t : ℝ) :
    0 < positiveSourceY t := by
  unfold positiveSourceY
  apply Real.sqrt_pos.2
  positivity

/-- The actual target W-coordinate on the positive source
branch is the POSITIVE square-root of the target quartic.
This is where the sign of the elliptic integrand is certified,
rather than silently using a formal square identity. -/
theorem period_target_positive_branch (t : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) :
    quarticW t (positiveSourceY t) =
      Real.sqrt ((1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2)) := by
  have hY := positiveSourceY_sq t
  have htarget :
      0 ≤ (1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2) := by positivity
  have hWsq := quartic_target_affine t (positiveSourceY t) ht hY
  have hWnonneg : 0 ≤ quarticW t (positiveSourceY t) := by
    unfold quarticW
    exact div_nonneg
      (mul_nonneg (by positivity) (le_of_lt (positiveSourceY_pos t)))
      (sq_nonneg _)
  have hroot_nonneg :
      0 ≤ Real.sqrt ((1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2)) := Real.sqrt_nonneg _
  have hroot_sq :
      (Real.sqrt ((1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2))) ^ 2 =
        (1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2) :=
    Real.sq_sqrt htarget
  nlinarith

/-- The actual real elliptic differential identity using the
correct positive square roots, valid at every real t with t² ≠ 1.
This is the pointwise integrand change-of-variable formula
underlying Eq. (555); NO period-integral equality is asserted. -/
theorem actual_positive_period_integrand (t : ℝ)
    (ht : 1 - t ^ 2 ≠ 0) :
    deriv quarticZ t /
      Real.sqrt ((1 + quarticZ t ^ 2) *
        (1 + 2 * quarticZ t ^ 2)) =
      Real.sqrt 2 / Real.sqrt (1 + t ^ 4) := by
  rw [← period_target_positive_branch t ht]
  exact quartic_differential_ratio t (positiveSourceY t)
    ht (ne_of_gt (positiveSourceY_pos t))

#print axioms Manuscript15.CrossQuarticPeriodDifferential20261125.positiveSourceY_sq
#print axioms Manuscript15.CrossQuarticPeriodDifferential20261125.positiveSourceY_pos
#print axioms Manuscript15.CrossQuarticPeriodDifferential20261125.period_target_positive_branch
#print axioms Manuscript15.CrossQuarticPeriodDifferential20261125.actual_positive_period_integrand

end Manuscript15.CrossQuarticPeriodDifferential20261125
