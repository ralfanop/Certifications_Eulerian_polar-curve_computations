import SpecialImaginaryPoint.V14119Priority3JointFredholmZeroStability

/-!
# Priority 3 — uniform quantitative SCALAR Fredholm reciprocal stability in two variables

For the actual universal complex Schatten-S₁ Fredholm determinant
 f_T(z)=det_F(I+zT) of any trace-class Hilbert operator T, the
certified joint operator/parameter bound E(T,S,z,w) controls
 |f_T(z)-f_S(w)|.

The same estimate gives (i) an a posteriori modulus separation from
zero and (ii) a finite upper bound for |1/f_T(z)| whenever E is less
than the genuine reference determinant modulus |f_S(w)|.

This conclusion is about the SCALAR Fredholm reciprocal, not the
operator resolvent. No normality, selfadjointness, positivity or
eigenvalue enumeration is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.JointFredholmReciprocalStability

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmJointVariation

/-- An a posteriori joint operator/complex spectral parameter lower
bound for the TRUE universal Fredholm determinant modulus. -/
theorem universalFredholm_joint_modulus_lower_bound
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet S w‖ -
      ((‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖)) ≤
      ‖fredholmDet T z‖ := by
  have h := universalFredholm_joint_diff_norm_le T S z w
  have htri : ‖fredholmDet S w‖ ≤
      ‖fredholmDet T z - fredholmDet S w‖ +
        ‖fredholmDet T z‖ := by
    calc
      ‖fredholmDet S w‖ =
          ‖(fredholmDet T z - fredholmDet S w) -
              fredholmDet T z‖ := by
        simp
      _ ≤ ‖fredholmDet T z - fredholmDet S w‖ +
          ‖fredholmDet T z‖ :=
        norm_sub_le _ _
  linarith

/-- Under an explicit small joint trace-norm / spectral-parameter
perturbation, the actual SCALAR Fredholm reciprocal is bounded
solely by the reference determinant modulus and joint error. -/
theorem universalFredholm_joint_reciprocal_bound
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hsmall :
      (‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖) <
        ‖fredholmDet S w‖) :
    ‖(fredholmDet T z)⁻¹‖ ≤
      1 / (‖fredholmDet S w‖ -
        ((‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖))) := by
  have hgap : 0 <
      ‖fredholmDet S w‖ -
        ((‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
        (‖z - w‖ * ‖S‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖)) := by
    linarith
  have hbound := universalFredholm_joint_modulus_lower_bound T S z w
  calc
    ‖(fredholmDet T z)⁻¹‖ = 1 / ‖fredholmDet T z‖ := by
      simp only [norm_inv, one_div]
    _ ≤ 1 /
        (‖fredholmDet S w‖ -
          ((‖z‖ * ‖T - S‖) *
            Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
          (‖z - w‖ * ‖S‖) *
            Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖))) :=
      one_div_le_one_div_of_le hgap hbound

#print axioms Manuscript14Priority3.JointFredholmReciprocalStability.universalFredholm_joint_modulus_lower_bound
#print axioms Manuscript14Priority3.JointFredholmReciprocalStability.universalFredholm_joint_reciprocal_bound

end Manuscript14Priority3.JointFredholmReciprocalStability
