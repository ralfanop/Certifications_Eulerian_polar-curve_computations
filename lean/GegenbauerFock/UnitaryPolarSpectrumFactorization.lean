import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — exact polar-type Hilbert factorization with positive spectral weights

The two genuine complete singular Hilbert bases give a unitary W from
ultraspherical L² to the full infinite Fock coefficient Hilbert space
and a bounded source operator P = W⁻¹ C. It has the positive real
singular weights sqrt(mu) on a COMPLETE Hilbert basis, satisfies
C = W P pointwise and squares to the genuine source Gram C†C.

This is an exact factorization, not a claim that C is surjective.
A separate continuous-functional-calculus identification P = |C|
can be added after its own rigorous positivity/uniqueness audit.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An explicit Hilbert-unitary phase W and bounded positive-spectrum
amplitude P realize the true C as W ∘ P, with P² = C†C.
The spectral squares have the exact Kummer sum. -/
theorem exists_unitary_positive_spectrum_factorization_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, W (u i) = v i) ∧
      (∀ i, P (u i) = (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  let W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
      InfiniteAnalysis.FockCoefficients := u.repr.trans v.repr.symm
  let P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
    W.symm.toContinuousLinearMap.comp (C lam alpha hlam ha)
  have hWu (i : ι) : W (u i) = v i := by
    change v.repr.symm (u.repr (u i)) = v i
    rw [u.repr_self, v.repr_symm_single]
  have hPu (i : ι) :
      P (u i) = (Real.sqrt (mu i) : ℂ) • u i := by
    change W.symm (C lam alpha hlam ha (u i)) = _
    rw [hC i, map_smul, ← hWu i, W.symm_apply_apply]
  have hsq (i : ι) : (Real.sqrt (mu i) : ℂ) ^ 2 = (mu i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hp i).le
  have hGs (i : ι) :
      gram lam alpha hlam ha (u i) = (mu i : ℂ) • u i := by
    change C_adjoint lam alpha hlam ha (C lam alpha hlam ha (u i)) = _
    rw [hC i, map_smul, hAdj i, smul_smul, ← pow_two, hsq i]
  have hP2 :
      P.comp P = gram lam alpha hlam ha := by
    apply ContinuousLinearMap.ext_on u.dense_span
    rintro _ ⟨i, rfl⟩
    change P (P (u i)) = gram lam alpha hlam ha (u i)
    rw [hPu i, map_smul, hPu i, smul_smul, ← pow_two, hsq i, hGs i]
  refine ⟨ι, u, v, mu, W, P, hp, hsum, hK, hWu, hPu, ?_, ?_⟩
  · intro f
    change C lam alpha hlam ha f = W (W.symm (C lam alpha hlam ha f))
    exact (W.apply_symm_apply (C lam alpha hlam ha f)).symm
  · intro f
    have h := congrArg
      (fun A : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam) => A f) hP2
    simpa only [ContinuousLinearMap.comp_apply] using h.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_unitary_positive_spectrum_factorization_kummer

end GegenbauerFock.GeneralUltrasphericalFock
