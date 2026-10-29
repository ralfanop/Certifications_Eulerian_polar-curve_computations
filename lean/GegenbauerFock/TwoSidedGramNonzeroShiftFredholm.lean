import GegenbauerFock.TwoSidedGramNonzeroFiniteEigenspaces
import GegenbauerFock.TwoSidedGramFredholmEssentialSpectrum
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# V007 — nonzero spectral shifts of both compact selfadjoint Grams are Fredholm

The fundamental operator-theoretic bridge:
for a compact symmetric complex Hilbert-space endomorphism T and μ ≠ 0,
the eigenspace P = ker(T-μI) is finite-dimensional. Its orthogonal
complement Q=Pᗮ is closed, finite-codimensional and T-invariant.
The restricted compact map T|Q has no μ-eigenvalue, so by the
Fredholm alternative μ belongs to its resolvent. The restriction
(T-μI)|Q is thus an invertible bounded operator.

Mathlib's IsFredholm.of_isInvertible_restrict then implies T-μI
is Fredholm. This proves that no nonzero spectral parameter lies in
the Fredholm essential spectrum, and applies to the ACTUAL
ultraspherical/Fock Grams acting on different Hilbert spaces.

This module is independently CI checked: do not claim a new certificate
until Lean has accepted its entire source and its #print axioms audit.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero spectral shift of a genuine compact symmetric
complex Hilbert-space endomorphism is Fredholm. -/
private theorem compact_symmetric_nonzero_shift_isFredholm
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hcompact : IsCompactOperator T)
    (hsymm : T.toLinearMap.IsSymmetric)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ContinuousLinearMap.IsFredholm
      (T - mu • (1 : H →L[ℂ] H)) := by
  let P : Submodule ℂ H := eigenspace T.toLinearMap mu
  let Q : Submodule ℂ H := Pᗮ
  let S : H →L[ℂ] H := T - mu • (1 : H →L[ℂ] H)
  haveI : FiniteDimensional ℂ P :=
    ContinuousLinearMap.finite_dimensional_eigenspace hcompact mu hmu
  haveI : CompleteSpace P :=
    (show IsClosed (P : Set H) from inferInstance).completeSpace_coe
  haveI : P.HasOrthogonalProjection := .ofCompleteSpace P
  haveI : CompleteSpace Q := P.isClosed_orthogonal.completeSpace_coe
  haveI : Q.CoFG := FG.cofg_of_isCompl P.isCompl_orthogonal .of_finite
  have hTQ : ∀ x ∈ Q, T x ∈ Q := by
    intro x hx
    exact hsymm.invariant_orthogonalComplement_eigenspace mu x hx
  let R : Q →L[ℂ] Q := T.restrict hTQ
  have hRcompact : IsCompactOperator R :=
    hcompact.restrict' hTQ
  have hRzero : eigenspace R.toLinearMap mu = ⊥ := by
    simpa only [R] using
      (eigenspace_restrict_eq_bot hTQ P.orthogonal_disjoint)
  have hRnoEigen : ¬ HasEigenvalue (R : Module.End ℂ Q) mu := by
    intro heig
    exact (hasEigenvalue_iff.mp heig) hRzero
  have hres : mu ∈ resolventSet ℂ R :=
    (hRcompact.hasEigenvalue_or_mem_resolventSet hmu).resolve_left hRnoEigen
  have hunit : IsUnit (R - mu • (1 : Q →L[ℂ] Q)) := by
    have hunit' : IsUnit (mu • (1 : Q →L[ℂ] Q) - R) := by
      simpa only [resolventSet, Set.mem_ofPred_eq,
        Algebra.algebraMap_eq_smul_one] using hres
    simpa only [neg_sub] using hunit'.neg
  have hSQ : ∀ x ∈ Q, S x ∈ Q := by
    intro x hx
    change T x - mu • x ∈ Q
    exact Q.sub_mem (hTQ x hx) (Q.smul_mem mu hx)
  have hrestrict : S.restrict hSQ = R - mu • (1 : Q →L[ℂ] Q) := by
    ext ⟨x, hx⟩
    rfl
  have hrestrInv : (S.restrict hSQ).IsInvertible := by
    rw [hrestrict]
    obtain ⟨u, hu⟩ := hunit
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  exact ContinuousLinearMap.IsFredholm.of_isInvertible_restrict
    P.isClosed_orthogonal P.isClosed_orthogonal hSQ hrestrInv

/-- The source ultraspherical L² Gram has Fredholm shifts at every
nonzero complex scalar. -/
theorem sourceGram_nonzero_shift_isFredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ContinuousLinearMap.IsFredholm
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) := by
  have hsym : (gram lam alpha hlam ha).toLinearMap.IsSymmetric := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
      (gram_selfadjoint lam alpha hlam ha)
  exact compact_symmetric_nonzero_shift_isFredholm
    (gram lam alpha hlam ha)
    (gram_compact_concrete lam alpha hlam ha)
    hsym mu hmu

/-- The full Gaussian–Fock coefficient output Gram also has Fredholm
shifts at every nonzero complex scalar. -/
theorem outputGram_nonzero_shift_isFredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ContinuousLinearMap.IsFredholm
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) := by
  have hsym : (outputGram lam alpha hlam ha).toLinearMap.IsSymmetric := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
      (outputGram_selfadjoint lam alpha hlam ha)
  exact compact_symmetric_nonzero_shift_isFredholm
    (outputGram lam alpha hlam ha)
    (outputGram_compact lam alpha hlam ha)
    hsym mu hmu

/-- For every nonzero spectral parameter, both actual distinct
Hilbert-space Grams have Fredholm shifts. -/
theorem two_sided_gram_nonzero_shifts_fredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ContinuousLinearMap.IsFredholm
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) ∧
    ContinuousLinearMap.IsFredholm
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) :=
  ⟨sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_shift_isFredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_shift_isFredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_shifts_fredholm

end GegenbauerFock.GeneralUltrasphericalFock
