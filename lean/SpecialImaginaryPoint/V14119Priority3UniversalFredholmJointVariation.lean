import SpecialImaginaryPoint.V14119Priority3UniversalFredholmExplicitZeroExclusion

/-!
# Priority 3 — genuine two-variable Fredholm determinant perturbation estimates

The actual CFC Schatten-S₁ Fredholm determinant f_T(z)=det_F(I+zT)
of arbitrary complex trace-class Hilbert operators is quantitatively
controlled under both types of perturbation:
* trace-class perturbation of its operator T;
* complex spectral-parameter perturbation z↦w.

The resulting two-variable estimate is finite-compression-independent
and does NOT require normality, positivity, selfadjointness or a
spectral eigenvalue enumeration.

This is the genuine infinite-dimensional Hilbert-compression-limit
determinant, not a scalar auxiliary product.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmJointVariation

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmSpectralVariation

/-- Genuine universal determinant trace-norm perturbation bound
for ANY pair of arbitrary complex CFC-S₁ operators. -/
theorem universalFredholm_two_operators_diff_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z - fredholmDet S z‖ ≤
      (‖z‖ * ‖T - S‖) *
        Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) := by
  have h := fredholmDet_add_traceNorm_bound S (T - S) z
  have hEq : S + (T - S) = T := by abel
  rwa [hEq] at h

/-- Two-variable global perturbation bound in BOTH trace-class
operator T and complex spectral parameter z, for the actual
infinite-dimensional Fredholm determinant. -/
theorem universalFredholm_joint_diff_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet T z - fredholmDet S w‖ ≤
      (‖z‖ * ‖T - S‖) *
        Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
      (‖z - w‖ * ‖S‖) *
        Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖) := by
  calc
    ‖fredholmDet T z - fredholmDet S w‖ =
        ‖(fredholmDet T z - fredholmDet S z) +
          (fredholmDet S z - fredholmDet S w)‖ := by
      congr 1
      ring
    _ ≤ ‖fredholmDet T z - fredholmDet S z‖ +
          ‖fredholmDet S z - fredholmDet S w‖ :=
      norm_add_le _ _
    _ ≤
        (‖z‖ * ‖T - S‖) *
            Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
          (‖z - w‖ * ‖S‖) *
            Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖) :=
      add_le_add
        (universalFredholm_two_operators_diff_norm_le T S z)
        (universalFredholm_spectral_diff_norm_le S z w)

#print axioms Manuscript14Priority3.UniversalFredholmJointVariation.universalFredholm_two_operators_diff_norm_le
#print axioms Manuscript14Priority3.UniversalFredholmJointVariation.universalFredholm_joint_diff_norm_le

end Manuscript14Priority3.UniversalFredholmJointVariation
