import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — matching real Gram eigenvalue families on the full singular bases

The exact positive singular Hilbert bases diagonalize BOTH actual
compact Grams, C†C and CC†, with the SAME index and the SAME
real eigenvalues, including multiplicities. Their unrestricted
spectral sum is the true Kummer mass.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine source and output compact Grams admit complete Hilbert
eigenbases indexed by the same type, with identical strictly positive
eigenvalue functions and exact unregularized Kummer spectral trace. -/
theorem exists_joint_gram_eigenHilbert_bases_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, gram lam alpha hlam ha (u i) = (mu i : ℂ) • u i) ∧
      (∀ i, outputGram lam alpha hlam ha (v i) = (mu i : ℂ) • v i) := by
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  have hsq (i : ι) : (Real.sqrt (mu i) : ℂ) ^ 2 = (mu i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hp i).le
  refine ⟨ι, u, v, mu, hp, hsum, hK, ?_, ?_⟩
  · intro i
    change C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha (u i)) = (mu i : ℂ) • u i
    rw [hC i, map_smul, hAdj i, smul_smul, ← pow_two, hsq]
  · intro i
    change C lam alpha hlam ha
      (C_adjoint lam alpha hlam ha (v i)) = (mu i : ℂ) • v i
    rw [hAdj i, map_smul, hC i, smul_smul, ← pow_two, hsq]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_joint_gram_eigenHilbert_bases_kummer

end GegenbauerFock.GeneralUltrasphericalFock
