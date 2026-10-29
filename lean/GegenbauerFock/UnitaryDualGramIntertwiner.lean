import GegenbauerFock.JointGramEigenHilbertBases

/-!
# V007 — exact Hilbert-unitary intertwiner for the two genuine compact Grams

The two complete Gram Hilbert eigenbases with matched positive spectral
multiplicity determine a unitary Hilbert-space equivalence W from the
original ultraspherical source L² to the full infinite Fock coefficient
Hilbert space. It maps source eigenvectors to output eigenvectors and
intertwines the ACTUAL bounded Gram operators C†C and CC† pointwise.

The unitary W is a separate operator from compact C; this result does
not claim that C is surjective or boundedly invertible.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true source and output Grams are unitarily intertwined across
their two original complete infinite Hilbert spaces. The unitary is
constructed from the common multiplicity-indexed complete eigenbases,
rather than postulated. -/
theorem exists_unitary_dualGram_intertwiner_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i : ι, W (u i) = v i) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        outputGram lam alpha hlam ha (W f) =
          W (gram lam alpha hlam ha f)) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hGs, hGo⟩ :=
    exists_joint_gram_eigenHilbert_bases_kummer lam alpha hlam ha
  let W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
      InfiniteAnalysis.FockCoefficients :=
    u.repr.trans v.repr.symm
  have hWu (i : ι) : W (u i) = v i := by
    change v.repr.symm (u.repr (u i)) = v i
    rw [u.repr_self, v.repr_symm_single]
  have hmaps :
      (outputGram lam alpha hlam ha).comp W.toLinearIsometry.toContinuousLinearMap =
        W.toLinearIsometry.toContinuousLinearMap.comp (gram lam alpha hlam ha) := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr u.dense_span)
    rintro _ ⟨i, rfl⟩
    change outputGram lam alpha hlam ha (W (u i)) =
      W (gram lam alpha hlam ha (u i))
    rw [hWu i, hGo i, hGs i, map_smul, hWu i]
  refine ⟨ι, u, v, mu, W, hp, hsum, hK, hWu, ?_⟩
  intro f
  have h := congrArg
    (fun A : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      InfiniteAnalysis.FockCoefficients => A f) hmaps
  simpa only [ContinuousLinearMap.comp_apply] using h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_unitary_dualGram_intertwiner_kummer

end GegenbauerFock.GeneralUltrasphericalFock
