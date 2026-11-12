import SpecialImaginaryPoint.V14119Priority3UniversalFredholmJointVariation

/-!
# Priority 3 — quantitative joint spectral/operator stability of genuine Fredholm zeros

Let f_T(z)=det_F(I+zT) denote the actual universal Hilbert-compression-
limit Fredholm determinant of an arbitrary complex CFC Schatten-S₁
trace-class Hilbert operator T.

The existing joint variation estimate yields a rigorous explicit margin:
if f_S(w) is nonzero, no simultaneous perturbation (S,w) → (T,z)
can create a determinant zero as long as the *joint* perturbation
bound stays strictly below the original determinant modulus.

Conversely every newly obtained zero forces the joint perturbation
bound to be at least the original determinant modulus. These results
do not claim continuity or differentiability of individual eigenvalue
branches, and apply to nonnormal and nonselfadjoint operators.
-/

noncomputable section

namespace Manuscript14Priority3.JointFredholmZeroStability

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmJointVariation

/-- Explicit robust nonvanishing under simultaneous perturbation
of the true trace-class operator and complex spectral parameter. -/
theorem universalFredholm_joint_nonzero_of_strict_margin
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hsmall :
      (‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖) <
        ‖fredholmDet S w‖) :
    fredholmDet T z ≠ 0 := by
  intro hz
  have hb := universalFredholm_joint_diff_norm_le T S z w
  simp only [hz, zero_sub, norm_neg] at hb
  exact (not_lt_of_ge hb) hsmall

/-- An actual zero after simultaneous operator/spectral perturbation
forces the global perturbation error to exceed the initial
Fredholm determinant modulus. -/
theorem universalFredholm_joint_zero_requires_large_variation
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hz : fredholmDet T z = 0) :
    ‖fredholmDet S w‖ ≤
      (‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖) := by
  have hb := universalFredholm_joint_diff_norm_le T S z w
  simpa only [hz, zero_sub, norm_neg] using hb

#print axioms Manuscript14Priority3.JointFredholmZeroStability.universalFredholm_joint_nonzero_of_strict_margin
#print axioms Manuscript14Priority3.JointFredholmZeroStability.universalFredholm_joint_zero_requires_large_variation

end Manuscript14Priority3.JointFredholmZeroStability
