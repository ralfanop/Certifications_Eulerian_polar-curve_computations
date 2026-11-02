import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatResolventCommutation
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventIntegratedCertificate
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitSymmetry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — compact symmetric heat-regularized canonical Sturm resolvent

For every lambda,t>0 and s≥0, the genuine weighted-real-L² operator

  H_s ∘ (t I - closure L₀)⁻¹

is compact and self-adjoint. The compactness comes from the previously
kernel-certified genuine compact resolvent and bounded heat evolution.
The self-adjointness comes from the genuine full-L² symmetry of both
factors and their independently proved exact commutation.

This is a claim about the actual operators on real weighted L², not
an auxiliary coefficient diagonal or an abstract spectral extension.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual heat-regularized positive-shift Gegenbauer Sturm
resolvent is compact and self-adjoint on the entire real weighted L². -/
theorem sturmRealHeatResolvent_compact_and_selfAdjoint
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 ≤ s) :
    IsCompactOperator
      ((sturmRealHeatLimitCLM lam hlam s hs).comp
        (sturmRealPositiveResolventFullCLM lam t hlam ht)) ∧
    IsSelfAdjoint
      ((sturmRealHeatLimitCLM lam hlam s hs).comp
        (sturmRealPositiveResolventFullCLM lam t hlam ht)) := by
  let T : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitCLM lam hlam s hs
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  have hcomm : T.comp R = R.comp T :=
    sturmRealHeatLimitCLM_comp_fullResolvent_comm lam t s hlam ht hs
  have hcompactR : IsCompactOperator R :=
    sturmRealClosedResolvent_isCompactOperator lam t hlam ht
  have hcompact : IsCompactOperator (T.comp R) := by
    rw [hcomm]
    exact hcompactR.comp_clm T
  have hsym : IsSelfAdjoint (T.comp R) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro f g
    change inner ℝ (T (R f)) g = inner ℝ f (T (R g))
    calc
      inner ℝ (T (R f)) g = inner ℝ (R f) (T g) :=
        sturmRealHeatLimitCLM_inner_symmetric
          lam hlam s hs (R f) g
      _ = inner ℝ f (R (T g)) :=
        sturmRealPositiveResolventFullCLM_inner_symmetric
          lam t hlam ht f (T g)
      _ = inner ℝ f (T (R g)) := by
        rw [← ContinuousLinearMap.comp_apply,
          ← ContinuousLinearMap.comp_apply, ← hcomm]
  exact ⟨hcompact, hsym⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatResolvent_compact_and_selfAdjoint

end GegenbauerFock.Ultraspherical
