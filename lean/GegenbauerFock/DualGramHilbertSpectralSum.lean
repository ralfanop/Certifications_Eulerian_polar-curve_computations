import GegenbauerFock.TwoSidedSingularSpectralCompleteness
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — bilateral Hilbert direct-sum spectral decomposition

For each genuine infinite-dimensional compact Gram, its complete
family of eigenspaces has dense sum, and the orthogonal family gives
a Hilbert direct-sum realization. The zero eigenspaces are already
proved trivial separately; this file does not manufacture an eigenbasis
or claim a multiplicity-indexed eigenvalue trace identity.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Dense algebraic sum of all source-Gram eigenspaces in the
true ultraspherical L² Hilbert space. -/
theorem sourceGram_eigenspaces_closure_top
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
       eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu
    ).topologicalClosure =
      (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  exact Submodule.topologicalClosure_eq_top_iff.mpr
    (gramIntegralOperator_eigenspaces_complete lam alpha hlam ha)

/-- Dense algebraic sum of all output-Gram eigenspaces in the
genuine coefficient Fock Hilbert space. -/
theorem outputGram_eigenspaces_closure_top
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
       eigenspace (outputGram lam alpha hlam ha).toLinearMap mu
    ).topologicalClosure =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  exact Submodule.topologicalClosure_eq_top_iff.mpr
    (outputGram_eigenspaces_complete lam alpha hlam ha)

/-- The source space is the Hilbert direct sum of its true compact
Gram eigenspaces, including the (trivial) zero sector. -/
theorem sourceGram_eigenspaces_isHilbertSum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsHilbertSum ℂ
      (fun mu : ℂ =>
         ↥(eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu))
      (fun mu : ℂ =>
         (eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
    (fun mu : ℂ =>
      eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)
    (gramIntegralOperator_orthogonal_eigenspaces lam alpha hlam ha)
  exact le_of_eq (sourceGram_eigenspaces_closure_top lam alpha hlam ha).symm

/-- The output Fock coefficient space is the Hilbert direct sum of
its true compact Gram eigenspaces. -/
theorem outputGram_eigenspaces_isHilbertSum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsHilbertSum ℂ
      (fun mu : ℂ =>
         ↥(eigenspace (outputGram lam alpha hlam ha).toLinearMap mu))
      (fun mu : ℂ =>
         (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
    (fun mu : ℂ =>
      eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (outputGram_symmetric lam alpha hlam ha))
  exact le_of_eq (outputGram_eigenspaces_closure_top lam alpha hlam ha).symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_eigenspaces_closure_top
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_eigenspaces_closure_top
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_eigenspaces_isHilbertSum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_eigenspaces_isHilbertSum

end GegenbauerFock.GeneralUltrasphericalFock
