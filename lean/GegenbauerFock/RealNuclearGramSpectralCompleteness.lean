import GegenbauerFock.RealNuclearGramCompactPositiveKernel
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# V007 — spectral completeness of the actual compact real nuclear Gram

For every real nuclear Hilbert operator T, the ACTUAL Gram
G = T†T is compact, positive-semidefinite and selfadjoint. The
infinite-dimensional compact selfadjoint spectral theorem of Mathlib
then gives total eigenspace span: its orthogonal complement is zero.

All nonzero eigenspaces have finite dimension and every eigenvalue is
nonnegative. These are real-space statements for G itself, without
assuming a global unitary phase or equal kernel/cokernel defects.

This does not construct |T| or a partial polar isometry; their
existence and the general singular-value summability converse are
separate later steps.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Module End

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Genuine compact-real-Gram eigenspaces span a dense subspace:
the orthogonal complement of the supremum of all eigenspaces vanishes.
This is the compact selfadjoint spectral theorem, not an extra axiom. -/
theorem HasRealNuclearRankOneSeries.gram_eigenspaces_complete
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T) :
    (⨆ μ : ℝ, eigenspace
      ((realNuclearGram T : H →L[ℝ] H) : Module.End ℝ H) μ)ᗮ = ⊥ := by
  have hSym : (realNuclearGram T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (realNuclearGram_isSelfAdjoint T)
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (hT.gram_isCompactOperator) hSym

/-- Every nonzero real eigenvalue of the genuine nuclear Gram
has a finite-dimensional eigenspace, with no assumption on ker(T). -/
theorem HasRealNuclearRankOneSeries.gram_nonzero_eigenspace_finite
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (μ : ℝ) (hμ : μ ≠ 0) :
    FiniteDimensional ℝ
      (eigenspace (realNuclearGram T).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (hT.gram_isCompactOperator) μ hμ

/-- The genuine real Gram has no negative eigenvalues, by its exact
quadratic-form positivity. -/
theorem realNuclearGram_eigenvalue_nonneg
    (T : H →L[ℝ] H) (μ : ℝ)
    (hμ : HasEigenvalue (realNuclearGram T : Module.End ℝ H) μ) :
    0 ≤ μ := by
  apply eigenvalue_nonneg_of_nonneg hμ
  intro x
  change 0 ≤ inner ℝ x (realNuclearGram T x)
  exact realNuclearGram_inner_nonneg T x

#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_eigenspaces_complete
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_nonzero_eigenspace_finite
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_eigenvalue_nonneg

end GegenbauerFock.Ultraspherical
