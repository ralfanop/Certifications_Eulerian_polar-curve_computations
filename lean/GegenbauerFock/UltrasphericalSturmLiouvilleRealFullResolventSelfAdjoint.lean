import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — self-adjointness of the exact bounded full-L² real Sturm resolvent

The certified closed Sturm spectral-graph theorem gives symmetry of
the genuine all-L² continuous resolvent, for every t > 0.
A bounded Hilbert-space operator is self-adjoint precisely when its
underlying linear map is symmetric. Thus the actual inverse of
tI - closure(A) is a self-adjoint bounded continuous linear map.

This is an unconditional statement about the exact real
ultraspherical Hilbert operator, not a truncated matrix model.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The full-space positive-shift resolvent of the true closed
ultraspherical Sturm operator is self-adjoint on weighted real L². -/
theorem sturmRealPositiveResolventFullCLM_isSelfAdjoint
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsSelfAdjoint (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  exact sturmRealPositiveResolventFullCLM_inner_symmetric
    lam t hlam ht f g

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_isSelfAdjoint

end GegenbauerFock.Ultraspherical
