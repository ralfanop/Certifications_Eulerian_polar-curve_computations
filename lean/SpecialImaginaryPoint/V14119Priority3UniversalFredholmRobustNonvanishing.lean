import SpecialImaginaryPoint.V14119Priority3UniversalFredholmJointVariation

/-!
# Priority 3 — robust nonvanishing under simultaneous trace-class and spectral perturbations

For the **genuine** universal CFC Schatten-S₁ Fredholm determinant
  D(T,z) = det_F(I+zT),
the already certified two-variable perturbation bound yields a quantified
zero-exclusion criterion about any nonzero *reference* value D(S,w).

Unlike a disk centered at zero, the region below is centered at an arbitrary
reference pair (S,w), and simultaneously allows arbitrary trace-class
operator perturbations and changes of the complex spectral parameter.

This is a classical consequence of the triangle inequality and the
existing determinant perturbation estimate, not a claimed novel theorem.
No spectral enumeration, selfadjointness, or positivity is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmRobustNonvanishing

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmJointVariation

/-- An explicit bound on the change of the *genuine* Fredholm
determinant in both the trace-class operator and its complex parameter. -/
def jointFredholmError
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ) : ℝ :=
  (‖z‖ * ‖T - S‖) *
    Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) +
  (‖z - w‖ * ‖S‖) *
    Real.exp ((‖w‖ + ‖z - w‖) * ‖S‖)

/-- Quantitative stability of the modulus: a reference Fredholm
determinant modulus, minus the explicit two-variable error, is a
lower bound for the perturbed genuine Fredholm determinant modulus. -/
theorem universalFredholm_joint_modulus_lower_bound
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet S w‖ - jointFredholmError T S z w ≤
      ‖fredholmDet T z‖ := by
  have hbound : ‖fredholmDet T z - fredholmDet S w‖ ≤
      jointFredholmError T S z w :=
    universalFredholm_joint_diff_norm_le T S z w
  apply sub_le_iff_le_add.mpr
  calc
    ‖fredholmDet S w‖ =
        ‖fredholmDet T z - (fredholmDet T z - fredholmDet S w)‖ := by
      congr 1
      ring
    _ ≤ ‖fredholmDet T z‖ +
          ‖fredholmDet T z - fredholmDet S w‖ :=
      norm_sub_le _ _
    _ ≤ ‖fredholmDet T z‖ + jointFredholmError T S z w := by
      exact add_le_add_left hbound ‖fredholmDet T z‖

/-- A genuine Fredholm zero at the perturbed pair forces the
reference determinant modulus to be no larger than the explicit
joint trace-class/spectral perturbation error. -/
theorem universalFredholm_joint_zero_requires_large_error
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hz : fredholmDet T z = 0) :
    ‖fredholmDet S w‖ ≤ jointFredholmError T S z w := by
  have h := universalFredholm_joint_diff_norm_le T S z w
  simpa [jointFredholmError, hz] using h

/-- A strictly positive quantitative margin at a reference
pair guarantees that the true universal Fredholm determinant stays
nonzero after simultaneous operator and spectral perturbations. -/
theorem universalFredholm_joint_nonzero_of_margin
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hmargin : jointFredholmError T S z w < ‖fredholmDet S w‖) :
    fredholmDet T z ≠ 0 := by
  intro hz
  exact (not_lt_of_ge
    (universalFredholm_joint_zero_requires_large_error T S z w hz)) hmargin

/-- Pointwise robust Fredholm zero-exclusion expressed as a
uniform set inclusion for all perturbed operator/parameter pairs. -/
theorem universalFredholm_joint_error_region_subset_nonzero
    (S : ProbabilisticTheory.TraceClass H) (w : ℂ) :
    {p : ProbabilisticTheory.TraceClass H × ℂ |
      jointFredholmError p.1 S p.2 w < ‖fredholmDet S w‖} ⊆
    {p : ProbabilisticTheory.TraceClass H × ℂ |
      fredholmDet p.1 p.2 ≠ 0} := by
  intro p hp
  exact universalFredholm_joint_nonzero_of_margin p.1 S p.2 w hp

#print axioms Manuscript14Priority3.UniversalFredholmRobustNonvanishing.universalFredholm_joint_modulus_lower_bound
#print axioms Manuscript14Priority3.UniversalFredholmRobustNonvanishing.universalFredholm_joint_zero_requires_large_error
#print axioms Manuscript14Priority3.UniversalFredholmRobustNonvanishing.universalFredholm_joint_nonzero_of_margin
#print axioms Manuscript14Priority3.UniversalFredholmRobustNonvanishing.universalFredholm_joint_error_region_subset_nonzero

end Manuscript14Priority3.UniversalFredholmRobustNonvanishing
