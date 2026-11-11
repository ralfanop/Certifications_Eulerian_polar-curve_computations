import SpecialImaginaryPoint.V14119Priority3UniversalFredholmExistence
import SpecialImaginaryPoint.V14119Priority3SpectralEquicontinuity

/-!
# Priority 3 — universal Fredholm spectral scalar covariance and nonzero stability

For arbitrary (also nonnormal and nonselfadjoint) CFC Schatten-S₁
Hilbert operators T,R and complex spectral parameter z, certify
the exact scalar-covariance identity

  det(I+zT) = det(I+(z • T))

as an equality of *universal* infinite-dimensional Fredholm
determinants, by passing equality of genuine finite Hilbert
compressions to their proved complex limits.

Additionally, the universal trace-norm perturbation estimate provides
a dimension-free, quantitative stability theorem: if the perturbation
majorant is strictly less than |det(I+zT)|, the perturbed determinant
is nonzero. This is a certified spectral nonvanishing criterion;
no invertibility equivalence is asserted.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalScalarCovariance

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.SpectralEquicontinuity
open Manuscript14Priority3.UniversalFredholmExistence

/-- Actual universal CFC-S₁ Fredholm determinant commutes exactly
with complex scalar multiplication of an arbitrary trace-class
operator, without matrix normality or rank assumptions. -/
theorem universal_fredholmDet_spectral_smul
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    fredholmDet T z = fredholmDet (z • T) 1 := by
  have hz := finiteDeterminant_tendsto_fredholmDet T z
  have hz' := finiteDeterminant_tendsto_fredholmDet (z • T) 1
  have hseq :
      (fun N : ℕ => finiteDeterminant N T z) =
        (fun N : ℕ => finiteDeterminant N (z • T) 1) :=
    funext (fun N => finiteDeterminant_spectral_smul N T z)
  rw [hseq] at hz
  exact tendsto_nhds_unique hz hz'

/-- Stability of NONZERO universal Fredholm determinants under any
actual CFC-S₁ trace-norm perturbation whose certified increment bound
does not reach the base determinant's modulus. -/
theorem universal_fredholmDet_nonzero_of_small_traceNorm_perturbation
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall : (‖z‖ * ‖R‖) *
      Real.exp (‖z‖ * (‖T‖ + ‖R‖)) < ‖fredholmDet T z‖) :
    fredholmDet (T + R) z ≠ 0 := by
  intro hzero
  have hbound := fredholmDet_add_traceNorm_bound T R z
  rw [hzero] at hbound
  simp only [zero_sub, norm_neg] at hbound
  exact (not_lt_of_ge hbound) hsmall

#print axioms Manuscript14Priority3.UniversalScalarCovariance.universal_fredholmDet_spectral_smul
#print axioms Manuscript14Priority3.UniversalScalarCovariance.universal_fredholmDet_nonzero_of_small_traceNorm_perturbation

end Manuscript14Priority3.UniversalScalarCovariance
