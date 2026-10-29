import GegenbauerFock.DualGramHilbertSpectralSum

/-!
# V007 — explicit unitary spectral Hilbert-sum coordinates

The certified Hilbert-sum decompositions are upgraded to concrete
linear isometry equivalences from the two original Hilbert spaces.
Single-support spectral vectors reconstruct the original eigenvectors
without any assumed global eigenbasis or artificial finite rank.
This prepares the construction of multiplicity-indexed eigenbases.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

noncomputable def sourceGramSpectralEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
      lp (fun mu : ℂ =>
        ↥(eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)) 2 :=
  (sourceGram_eigenspaces_isHilbertSum lam alpha hlam ha).linearIsometryEquiv

noncomputable def outputGramSpectralEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    InfiniteAnalysis.FockCoefficients ≃ₗᵢ[ℂ]
      lp (fun mu : ℂ =>
        ↥(eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)) 2 :=
  (outputGram_eigenspaces_isHilbertSum lam alpha hlam ha).linearIsometryEquiv

/-- A coordinate supported in one source Gram eigenspace is exactly
its eigenvector when reconstructed into the original L² Hilbert space. -/
theorem sourceGramSpectralEquiv_symm_single
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (v : eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) :
    (sourceGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v) =
      (v : Lp ℂ 2 (Ultraspherical.measure lam)) := by
  classical
  exact (sourceGram_eigenspaces_isHilbertSum lam alpha hlam ha)
    .linearIsometryEquiv_symm_apply_single v

/-- The corresponding output spectral coordinate reconstructs
the original entire-coefficient Fock Gram eigenvector. -/
theorem outputGramSpectralEquiv_symm_single
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (v : eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :
    (outputGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v) =
      (v : InfiniteAnalysis.FockCoefficients) := by
  classical
  exact (outputGram_eigenspaces_isHilbertSum lam alpha hlam ha)
    .linearIsometryEquiv_symm_apply_single v

/-- Exact source Gram eigen-equation for a genuinely reconstructed
one-coordinate Hilbert-sum vector, with no eigenvector hypothesis. -/
theorem sourceGramSpectralEquiv_single_eigen
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (v : eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) :
    gramIntegralOperator lam alpha hlam ha
      ((sourceGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v)) =
      mu • (sourceGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v) := by
  rw [sourceGramSpectralEquiv_symm_single]
  exact (mem_eigenspace_iff.mp v.property)

/-- Exact output Gram eigen-equation in the full coefficient Hilbert
space for a reconstructed one-coordinate spectral vector. -/
theorem outputGramSpectralEquiv_single_eigen
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (v : eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :
    outputGram lam alpha hlam ha
      ((outputGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v)) =
      mu • (outputGramSpectralEquiv lam alpha hlam ha).symm (lp.single 2 mu v) := by
  rw [outputGramSpectralEquiv_symm_single]
  exact (mem_eigenspace_iff.mp v.property)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramSpectralEquiv
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramSpectralEquiv
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramSpectralEquiv_symm_single
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramSpectralEquiv_symm_single
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramSpectralEquiv_single_eigen
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramSpectralEquiv_single_eigen

end GegenbauerFock.GeneralUltrasphericalFock
