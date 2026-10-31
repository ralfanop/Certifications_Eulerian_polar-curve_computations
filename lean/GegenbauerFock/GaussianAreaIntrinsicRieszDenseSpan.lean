import GegenbauerFock.GaussianAreaIntrinsicRieszSeparates
import GegenbauerFock.GaussianAreaEntireRadialCoefficientDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# V007 — the intrinsic reproducing vectors have dense linear span

The genuine complex Gaussian-L² holomorphic Hilbert space is already
isometric to the complete Fock coefficient model. The intrinsic Riesz
vectors reproduce the true entire representatives at every complex
point. A vector orthogonal to their span therefore has an identically
vanishing entire representative, hence is zero.

This proves density of the span of Riesz vectors without assuming a
polynomial-density premise in the proof.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The closed complex linear span of the genuine Riesz reproducing
vectors is the whole independently defined entire Gaussian-L²
Bargmann–Fock Hilbert space. -/
theorem intrinsicRieszKernel_span_dense
    (alpha : ℝ) (ha : 0 < alpha) :
    (Submodule.span ℂ
      (Set.range (intrinsicRieszKernel alpha ha))).topologicalClosure =
      (⊤ : Submodule ℂ (entireGaussianL2Submodule alpha)) := by
  let S : Submodule ℂ (entireGaussianL2Submodule alpha) :=
    Submodule.span ℂ (Set.range (intrinsicRieszKernel alpha ha))
  change S.topologicalClosure = ⊤
  -- The intrinsic entire Gaussian submodule was independently proved
  -- equal to the closed Gaussian polynomial span. Materialize its
  -- completeness rather than searching for it through typeclass synthesis.
  letI : CompleteSpace (entireGaussianL2Submodule alpha) := by
    rw [intrinsicEntire_eq_polynomialClosure_via_radial_inner alpha ha]
    unfold gaussianPolynomialClosure
    infer_instance
  letI : CompleteSpace S.topologicalClosure := inferInstance
  haveI : S.topologicalClosure.HasOrthogonalProjection := inferInstance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : x = 0 := by
    apply (intrinsicRieszKernel_pairings_zero_iff alpha ha x).mp
    intro z
    have hz : intrinsicRieszKernel alpha ha z ∈ S.topologicalClosure := by
      apply Submodule.le_topologicalClosure S
      exact Submodule.subset_span ⟨z, rfl⟩
    exact hx _ hz
  exact (Submodule.mem_bot ℂ).mpr hzero

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_span_dense

end GegenbauerFock.GaussianArea
