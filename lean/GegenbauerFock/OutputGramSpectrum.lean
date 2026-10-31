import GegenbauerFock.GramSingularTransfer

/-!
# V007: compact positive dual Gram and its infinite-dimensional spectrum

The genuine coefficient-side operator CC† is itself compact, positive,
and self-adjoint. Its eigenspaces form a complete spectral system and
every nonzero eigenspace is finite dimensional. These properties are
derived from compactness of the actual ultraspherical Fock analysis
map C and its genuine Hilbert adjoint, without postulating a finite
matrix or replacing the target by an abstract isometric model.

This theorem does not yet enumerate or normalize the singular pairs.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine coefficient-side Gram CC† is compact. -/
theorem outputGram_compact
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (outputGram lam alpha hlam ha) := by
  change IsCompactOperator
    (fun F => C lam alpha hlam ha (C_adjoint lam alpha hlam ha F))
  exact (C_compact lam alpha hlam ha).comp_clm
    (C_adjoint lam alpha hlam ha)

/-- The output Gram CC† is selfadjoint in the infinite coefficient
Hilbert space, not merely a finite truncation. -/
theorem outputGram_selfadjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (outputGram lam alpha hlam ha).adjoint =
      outputGram lam alpha hlam ha := by
  unfold outputGram C_adjoint
  simp

/-- The coefficient-side operator CC† is a genuine positive
Hilbert-space endomorphism. -/
theorem outputGram_isPositive
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (outputGram lam alpha hlam ha).IsPositive := by
  have hadj :
      (C_adjoint lam alpha hlam ha).adjoint =
        C lam alpha hlam ha := by
    unfold C_adjoint
    simp
  change ((C lam alpha hlam ha).comp
    (C_adjoint lam alpha hlam ha)).IsPositive
  rw [← hadj]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (C_adjoint lam alpha hlam ha)

/-- The coefficient-side Gram is symmetric in the sense needed
for Mathlib's infinite-dimensional compact spectral theorem. -/
theorem outputGram_symmetric
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((outputGram lam alpha hlam ha :
      InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) :
      InfiniteAnalysis.FockCoefficients →ₗ[ℂ]
        InfiniteAnalysis.FockCoefficients).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    (outputGram_selfadjoint lam alpha hlam ha)

/-- Every nonzero eigenspace of the *actual* coefficient-side compact
positive Gram is finite dimensional. -/
theorem outputGram_nonzero_eigenspace_finite
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (outputGram_compact lam alpha hlam ha) mu hmu

/-- Spectral completeness of all eigenspaces of the output Gram CC†.
This includes any possible zero eigenspace and makes NO unjustified
claim that the image of C is dense. -/
theorem outputGram_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
        eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (outputGram_compact lam alpha hlam ha)
    (outputGram_symmetric lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_compact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_isPositive
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_symmetric
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspace_finite
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_eigenspaces_complete

end GegenbauerFock.GeneralUltrasphericalFock
