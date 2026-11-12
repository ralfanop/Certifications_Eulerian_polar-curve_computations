import SpecialImaginaryPoint.V14119Priority3UniversalFredholmJointVariation
import SpecialImaginaryPoint.V14119Priority3SpectralEquicontinuity

/-!
# Priority 3 — exact complex scalar covariance of genuine universal Fredholm determinant

For every arbitrary (possibly nonnormal and nonselfadjoint) complex
CFC Schatten-S₁ Hilbert operator T, the actual universal Fredholm
determinant built as the limit of Hilbert compression determinants
commutes with complex scalar scaling of the operator:

  det_F(I + zT) = det_F(I + 1(zT)),
  det_F(I + z(aT)) = det_F(I + (za)T).

No finite-rank, diagonal or spectral enumeration assumption is used.
The equalities are derived by passing the ALREADY CERTIFIED exact
finite-compression identity to the unique universal limit.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmComplexScaleCovariance

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.SpectralEquicontinuity

/-- The genuine universal CFC-S₁ Fredholm determinant commutes with
complex scaling inside the operator, with spectral parameter 1. -/
theorem universalFredholm_spectral_smul
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    fredholmDet T z = fredholmDet (z • T) 1 := by
  have hfin :
      (fun N : ℕ => finiteDeterminant N T z) =
        (fun N : ℕ => finiteDeterminant N (z • T) 1) := by
    funext N
    exact finiteDeterminant_spectral_smul N T z
  have hlim := finiteDeterminant_tendsto_fredholmDet T z
  rw [hfin] at hlim
  exact tendsto_nhds_unique hlim
    (finiteDeterminant_tendsto_fredholmDet (z • T) 1)

/-- Exact two-scalar covariance of the genuine infinite-dimensional
Fredholm determinant for arbitrary nonnormal CFC-S₁ operators. -/
theorem universalFredholm_operator_smul
    (T : ProbabilisticTheory.TraceClass H) (a z : ℂ) :
    fredholmDet (a • T) z = fredholmDet T (z * a) := by
  calc
    fredholmDet (a • T) z =
        fredholmDet (z • (a • T)) 1 :=
      universalFredholm_spectral_smul (a • T) z
    _ = fredholmDet ((z * a) • T) 1 := by rw [smul_smul]
    _ = fredholmDet T (z * a) :=
      (universalFredholm_spectral_smul T (z * a)).symm

#print axioms Manuscript14Priority3.UniversalFredholmComplexScaleCovariance.universalFredholm_spectral_smul
#print axioms Manuscript14Priority3.UniversalFredholmComplexScaleCovariance.universalFredholm_operator_smul

end Manuscript14Priority3.UniversalFredholmComplexScaleCovariance
