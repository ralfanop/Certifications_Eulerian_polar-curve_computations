import GegenbauerFock.DualGramEigenbasisTrace
import GegenbauerFock.TwoSidedSingularSpectralCompleteness
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# V007 — complete real eigenvector Hilbert bases for the true compact Grams

A compact symmetric operator on a complete complex Hilbert space admits
a full Hilbert basis of eigenvectors.  The proof here assembles Hilbert
bases of each actual eigenspace using their orthogonal family and the
compact spectral theorem; it does not postulate a global eigenbasis.

Specializations apply to the true Gegenbauer–Fock source and output
Gram operators on two distinct infinite-dimensional Hilbert spaces.
The resulting eigenvalue index family repeats each spectral value by
its eigenspace multiplicity.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.HilbertSchmidtBasis

universe u

variable {H : Type u} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A genuine compact symmetric bounded operator has a complete
Hilbert basis of eigenvectors with REAL eigenvalues, indexed so that
the multiplicity of each eigenvalue is represented by basis vectors. -/
theorem exists_compact_realEigenHilbertBasis
    (T : H →L[ℂ] H) (hc : IsCompactOperator T)
    (hs : (T : H →ₗ[ℂ] H).IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (eig : ι → ℝ),
      ∀ i : ι, T (b i) = (eig i : ℂ) • b i := by
  classical
  let S : ℂ → Submodule ℂ H := fun μ => eigenspace T.toLinearMap μ
  have hchoice :
      ∀ μ : ℂ, ∃ (w : Set (S μ))
        (b : HilbertBasis w ℂ (S μ)), ⇑b = ((↑) : w → S μ) := by
    intro μ
    exact exists_hilbertBasis ℂ (S μ)
  choose W b hb using hchoice
  let ι : Type u := Σ μ : ℂ, W μ
  let v : ι → H := fun a => (b a.1 a.2 : H)
  have hfam : OrthogonalFamily ℂ
      (fun μ : ℂ => S μ) (fun μ => (S μ).subtypeₗᵢ) := by
    exact hs.orthogonalFamily_eigenspaces
  have hv : Orthonormal ℂ v := by
    simpa only [v, S] using
      hfam.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)
  have hsub (μ : ℂ) :
      S μ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    intro x hx
    let y : S μ := ⟨x, hx⟩
    have hsum : HasSum
        (fun i : W μ => ((b μ).repr y i) • (b μ i : H)) x := by
      have ht := ((S μ).subtypeL).hasSum ((b μ).hasSum_repr y)
      simpa only [map_smul] using ht
    refine mem_closure_of_tendsto hsum (Eventually.of_forall ?_)
    intro z
    simp only [SetLike.mem_coe]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨μ, i⟩, rfl⟩
  have hspec : (⨆ μ : ℂ, S μ)ᗮ = (⊥ : Submodule ℂ H) := by
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs
  have hspan : (Submodule.span ℂ (Set.range v))ᗮ =
      (⊥ : Submodule ℂ H) := by
    have hi : (⨆ μ : ℂ, S μ) ≤
        (Submodule.span ℂ (Set.range v)).topologicalClosure :=
      iSup_le hsub
    have hle := Submodule.orthogonal_le hi
    simp only [Submodule.orthogonal_closure, hspec] at hle
    exact le_antisymm hle bot_le
  let B : HilbertBasis ι ℂ H :=
    HilbertBasis.mkOfOrthogonalEqBot hv hspan
  let eigenvalue : ι → ℝ := fun a => a.1.re
  refine ⟨ι, B, eigenvalue, ?_⟩
  intro a
  have hmem : v a ∈ eigenspace T.toLinearMap a.1 := by
    exact (b a.1 a.2).property
  have heig : T (v a) = a.1 • v a :=
    (mem_eigenspace_iff).mp hmem
  have hne : v a ≠ 0 := by
    intro hz
    have hn := hv.1 a
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hreal : ((a.1.re : ℝ) : ℂ) = a.1 := by
    rw [← RCLike.conj_eq_iff_re]
    exact hs.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        (show HasEigenvector T.toLinearMap a.1 (v a) from ⟨hmem, hne⟩))
  simpa only [B, eigenvalue, HilbertBasis.coe_mkOfOrthogonalEqBot, hreal]
    using heig

#print axioms GegenbauerFock.HilbertSchmidtBasis.exists_compact_realEigenHilbertBasis

end GegenbauerFock.HilbertSchmidtBasis

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true source Gram has a complete real-eigenvalue Hilbert basis,
and its (multiplicity-counted) eigenvalue sum is unregularized Kummer. -/
theorem exists_sourceGram_eigenHilbertBasis_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (eig : ι → ℝ),
      (∀ i : ι, gram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) ∧
        Summable eig ∧
          (∑' i : ι, eig i) =
            KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  have hc : IsCompactOperator (gram lam alpha hlam ha) := by
    rw [gram_eq_gramIntegralOperator lam alpha hlam ha]
    exact gramIntegralOperator_compact lam alpha hlam ha
  have hs : ((gram lam alpha hlam ha) :
      Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsSymmetric := by
    rw [gram_eq_gramIntegralOperator lam alpha hlam ha]
    exact gramIntegralOperator_symmetric lam alpha hlam ha
  obtain ⟨ι, b, eig, heig⟩ :=
    HilbertSchmidtBasis.exists_compact_realEigenHilbertBasis
      (gram lam alpha hlam ha) hc hs
  refine ⟨ι, b, eig, heig, ?_, ?_⟩
  · exact sourceGram_realEigenvalues_summable lam alpha hlam ha b eig heig
  · exact sourceGram_realEigenvalues_tsum_eq_kummer lam alpha hlam ha b eig heig

/-- The genuine coefficient-space output Gram also has a complete
real-eigenvalue Hilbert basis with the SAME Kummer trace, with no
identification of the two underlying Hilbert spaces. -/
theorem exists_outputGram_eigenHilbertBasis_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (eig : ι → ℝ),
      (∀ i : ι, outputGram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) ∧
        Summable eig ∧
          (∑' i : ι, eig i) =
            KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  obtain ⟨ι, b, eig, heig⟩ :=
    HilbertSchmidtBasis.exists_compact_realEigenHilbertBasis
      (outputGram lam alpha hlam ha)
      (outputGram_compact lam alpha hlam ha)
      (outputGram_symmetric lam alpha hlam ha)
  refine ⟨ι, b, eig, heig, ?_, ?_⟩
  · exact outputGram_realEigenvalues_summable lam alpha hlam ha b eig heig
  · exact outputGram_realEigenvalues_tsum_eq_kummer lam alpha hlam ha b eig heig

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_sourceGram_eigenHilbertBasis_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_outputGram_eigenHilbertBasis_kummer

end GegenbauerFock.GeneralUltrasphericalFock
