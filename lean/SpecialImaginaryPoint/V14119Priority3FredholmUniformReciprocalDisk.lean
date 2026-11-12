import SpecialImaginaryPoint.V14119Priority3FredholmQuantitativeReciprocal

/-!
# Priority 3 — explicit UNIFORM scalar Fredholm reciprocal bound on a spectral disk

For any complex trace-class Hilbert operator T, with no normality or
positivity assumptions, the genuine CFC Schatten-S₁ Fredholm determinant
f_T(z)=det_F(I+zT) satisfies a quantitative global modulus lower bound.

A single trace-norm condition at a disk radius R,
  (R‖T‖)exp(R‖T‖)<1,
then yields for EVERY spectral parameter z in the closed disk |z|≤R:
  f_T(z)≠0 and |f_T(z)⁻¹|≤1/(1-(R‖T‖)exp(R‖T‖)).

Thus one explicit real margin controls the reciprocal of the ACTUAL
infinite-dimensional Fredholm determinant simultaneously on a disk.
The reciprocal is scalar; no operator inverse norm is asserted.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmUniformReciprocalDisk

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.QuantitativeFredholmNonvanishing
open Manuscript14Priority3.FredholmQuantitativeReciprocal

/-- The dimension-free trace-norm Fredholm error function is monotone
with respect to the magnitude of the complex spectral parameter,
for every nonnegative real radius. -/
theorem universalFredholm_exp_error_mono
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) (R : ℝ)
    (hzR : ‖z‖ ≤ R) :
    (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) ≤
      (R * ‖T‖) * Real.exp (R * ‖T‖) := by
  have hm : ‖z‖ * ‖T‖ ≤ R * ‖T‖ :=
    mul_le_mul_of_nonneg_right hzR (norm_nonneg T)
  have hExp : Real.exp (‖z‖ * ‖T‖) ≤ Real.exp (R * ‖T‖) :=
    Real.exp_le_exp.mpr hm
  have hRnonneg : 0 ≤ R := (norm_nonneg z).trans hzR
  exact mul_le_mul hm hExp (Real.exp_pos _).le
    (mul_nonneg hRnonneg (norm_nonneg T))

/-- A single explicit trace-norm condition on R excludes ALL
actual Fredholm determinant zeros inside |z|≤R simultaneously. -/
theorem universalFredholm_nonzero_on_quantitative_closedDisk
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ)
    (hR : (R * ‖T‖) * Real.exp (R * ‖T‖) < 1) :
    ∀ z : ℂ, ‖z‖ ≤ R → fredholmDet T z ≠ 0 := by
  intro z hz
  apply universalFredholm_nonzero_of_quantitative_bound T z
  exact (universalFredholm_exp_error_mono T z R hz).trans_lt hR

/-- Explicit uniform scalar reciprocal estimate on a full genuine
Fredholm zero-free disk, independent of the point z within the disk. -/
theorem universalFredholm_reciprocal_uniform_closedDisk
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ)
    (hR : (R * ‖T‖) * Real.exp (R * ‖T‖) < 1) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(fredholmDet T z)⁻¹‖ ≤
        1 / (1 - (R * ‖T‖) * Real.exp (R * ‖T‖)) := by
  intro z hz
  have herror :=
    universalFredholm_exp_error_mono T z R hz
  have hsmall := herror.trans_lt hR
  have hbound := universalFredholm_reciprocal_norm_bound T z hsmall
  have hRpos : 0 < 1 - (R * ‖T‖) * Real.exp (R * ‖T‖) := by
    linarith
  have hden :
      1 - (R * ‖T‖) * Real.exp (R * ‖T‖) ≤
        1 - (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
    linarith
  exact hbound.trans (one_div_le_one_div_of_le hRpos hden)

#print axioms Manuscript14Priority3.FredholmUniformReciprocalDisk.universalFredholm_exp_error_mono
#print axioms Manuscript14Priority3.FredholmUniformReciprocalDisk.universalFredholm_nonzero_on_quantitative_closedDisk
#print axioms Manuscript14Priority3.FredholmUniformReciprocalDisk.universalFredholm_reciprocal_uniform_closedDisk

end Manuscript14Priority3.FredholmUniformReciprocalDisk
