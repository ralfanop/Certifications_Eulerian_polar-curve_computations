import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramEssentialSpectrum
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramSpectral
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# V007 — exact Fredholm essential spectrum of the genuine holomorphic output Gram

The actual output Gram of the compact ultraspherical-to-entire-Gaussian
Fock transform acts on the complete intrinsic holomorphic Hilbert space,
not an abstract coefficient replacement. Its zero shift is non-Fredholm
by its independently certified dense, proper, nonclosed range.

For every nonzero complex shift, compact self-adjoint spectral theory
gives finite-dimensional eigenspace P, a finite-codimensional invariant
orthogonal complement Pᗮ, and an invertible restriction of the spectral
shift to Pᗮ. The Fredholm criterion then closes the argument.

The resulting Fredholm essential spectrum is exactly {0}.
This is stronger than the previously certified membership of zero.
-/

noncomputable section
open MeasureTheory Module End Submodule

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A compact symmetric complex Hilbert endomorphism has a Fredholm
shift at each nonzero complex parameter. A local proof is deliberately
provided, so the true intrinsic analytic Hilbert space is independently
auditable without depending on a private lemma about coefficient Grams. -/
private theorem compact_intrinsic_holomorphic_nonzero_shift_isFredholm
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
  have hRlin : R.toLinearMap = T.toLinearMap.restrict hTQ := by
    ext ⟨x, hx⟩
    rfl
  have hRzero : eigenspace R.toLinearMap mu = ⊥ := by
    rw [hRlin]
    exact eigenspace_restrict_eq_bot hTQ P.orthogonal_disjoint
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

/-- Every nonzero complex spectral shift of the genuine entire Gaussian
output Gram is Fredholm in the actual intrinsic Bargmann–Fock space. -/
theorem C_intrinsicEntire_outputGram_nonzero_shift_isFredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     ContinuousLinearMap.IsFredholm
       (C_intrinsicEntire_outputGram lam alpha hlam ha -
         mu • (1 : GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
           GaussianArea.entireGaussianL2Submodule alpha))) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact compact_intrinsic_holomorphic_nonzero_shift_isFredholm
    (C_intrinsicEntire_outputGram lam alpha hlam ha)
    (C_intrinsicEntire_outputGram_compact lam alpha hlam ha)
    (C_intrinsicEntire_outputGram_symmetric lam alpha hlam ha)
    mu hmu

/-- The full Fredholm essential spectrum on the TRUE holomorphic
Gaussian L² output Hilbert space equals the singleton {0}. -/
theorem C_intrinsicEntire_outputGram_fredholm_essential_eq_singleton_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     fredholmEssentialSpectrum
       (C_intrinsicEntire_outputGram lam alpha hlam ha) =
       ({0} : Set ℂ)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  ext mu
  constructor
  · intro hmu
    by_contra hne
    have hmu_ne : mu ≠ 0 := by simpa using hne
    exact hmu
      (C_intrinsicEntire_outputGram_nonzero_shift_isFredholm
        lam alpha hlam ha mu hmu_ne)
  · intro hmu
    have hzero : mu = 0 := by simpa using hmu
    subst mu
    exact C_intrinsicEntire_outputGram_zero_mem_fredholm_essential
      lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_nonzero_shift_isFredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_fredholm_essential_eq_singleton_zero

end GegenbauerFock.GeneralUltrasphericalFock
