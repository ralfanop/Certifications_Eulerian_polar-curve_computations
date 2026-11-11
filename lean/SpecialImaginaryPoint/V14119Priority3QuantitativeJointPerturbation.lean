import SpecialImaginaryPoint.V14119Priority3UniversalJointContinuity

/-!
# Priority 3 — quantitative JOINT trace-class and spectral Fredholm stability

A uniform and explicit two-parameter perturbation bound for the
universal genuine CFC Schatten-S₁ Fredholm determinant controls
simultaneous operator and complex-spectral parameter changes.

For arbitrary nonnormal trace-class T,R and complex z,w,
|det(I+(z+w)(T+R))-det(I+zT)| ≤
  |w| ||T+R||₁ exp((|z|+|w|)||T+R||₁)
  + |z| ||R||₁ exp(|z| (||T||₁+||R||₁)).

Further, for a spectral disk of radius ρ≥0 the entire determinant
z↦det(I+zT) is Lipschitz on that disk with the dimension-free
constant ||T||₁ exp(3ρ||T||₁). This supplies quantitative joint
sensitivity and uniform control on compact z-sets.
-/

noncomputable section

namespace Manuscript14Priority3.QuantitativeJointPerturbation

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalJointContinuity

/-- Simultaneous perturbation in the TRUE Schatten-S₁ norm and in
the complex spectral parameter, with explicit nonasymptotic
dimension-free exponential majorants. -/
theorem universal_fredholmDet_joint_perturbation_bound
    (T R : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet (T + R) (z + w) - fredholmDet T z‖ ≤
      (‖w‖ * ‖T + R‖) *
        Real.exp ((‖z‖ + ‖w‖) * ‖T + R‖) +
      (‖z‖ * ‖R‖) *
        Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
  have hspec := fredholmDet_spectral_diff_norm_le
    (T + R) (z + w) z
  have hzw : z + w - z = w := by abel
  rw [hzw] at hspec
  have htrace := fredholmDet_add_traceNorm_bound T R z
  calc
    ‖fredholmDet (T + R) (z + w) - fredholmDet T z‖ =
        ‖(fredholmDet (T + R) (z + w) -
            fredholmDet (T + R) z) +
          (fredholmDet (T + R) z - fredholmDet T z)‖ := by
      congr 1
      ring
    _ ≤ ‖fredholmDet (T + R) (z + w) -
          fredholmDet (T + R) z‖ +
        ‖fredholmDet (T + R) z - fredholmDet T z‖ :=
      norm_add_le _ _
    _ ≤ (‖w‖ * ‖T + R‖) *
        Real.exp ((‖z‖ + ‖w‖) * ‖T + R‖) +
      (‖z‖ * ‖R‖) *
        Real.exp (‖z‖ * (‖T‖ + ‖R‖)) :=
      add_le_add hspec htrace

/-- Uniform local Lipschitz constant on the full closed complex
disk of arbitrary nonnegative radius ρ, with NO matrix dimension
or operator normality hypothesis. -/
theorem universal_fredholmDet_spectral_disk_lipschitz
    (T : ProbabilisticTheory.TraceClass H) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (z w : ℂ)
    (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖fredholmDet T z - fredholmDet T w‖ ≤
      (‖z - w‖ * ‖T‖) *
        Real.exp ((3 * ρ) * ‖T‖) := by
  have hnorm := norm_sub_le z w
  have hthree : ‖w‖ + ‖z - w‖ ≤ 3 * ρ := by
    linarith
  have hexp : Real.exp ((‖w‖ + ‖z - w‖) * ‖T‖) ≤
      Real.exp ((3 * ρ) * ‖T‖) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hthree (norm_nonneg T))
  calc
    ‖fredholmDet T z - fredholmDet T w‖ ≤
        (‖z - w‖ * ‖T‖) *
          Real.exp ((‖w‖ + ‖z - w‖) * ‖T‖) :=
      fredholmDet_spectral_diff_norm_le T z w
    _ ≤ (‖z - w‖ * ‖T‖) *
        Real.exp ((3 * ρ) * ‖T‖) :=
      mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (norm_nonneg (z - w)) (norm_nonneg T))

#print axioms Manuscript14Priority3.QuantitativeJointPerturbation.universal_fredholmDet_joint_perturbation_bound
#print axioms Manuscript14Priority3.QuantitativeJointPerturbation.universal_fredholmDet_spectral_disk_lipschitz

end Manuscript14Priority3.QuantitativeJointPerturbation
