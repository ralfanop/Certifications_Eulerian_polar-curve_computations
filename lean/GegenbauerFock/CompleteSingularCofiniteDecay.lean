import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — cofinite spectral decay of genuine Gram singular values

The positive eigenvalues of the genuine compact Gegenbauer--Fock
source Gram, counted by a complete common singular Hilbert-basis
index, form a summable family. Hence their values tend to zero
along the cofinite filter, and each strictly positive threshold
has only finitely many eigenvectors (with multiplicity). This
uses no chosen ordering or artificial finite truncation.
-/

noncomputable section
open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Multiplicity-indexed true Gram eigenvalues vanish in the
cofinite-filter sense. Every positive spectral threshold supports
only finitely many singular modes; the common trace remains Kummer.
The source and target singular bases are complete. -/
theorem exists_complete_singular_cofinite_spectral_decay_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      Tendsto mu Filter.cofinite (𝓝 (0 : ℝ)) ∧
      (∀ eps : ℝ, 0 < eps → {i : ι | eps ≤ mu i}.Finite) ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (u i) =
        (Real.sqrt (mu i) : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) =
        (Real.sqrt (mu i) : ℂ) • u i) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  have hlim : Tendsto mu Filter.cofinite (𝓝 (0 : ℝ)) :=
    hsum.tendsto_cofinite_zero
  have hfin (eps : ℝ) (heps : 0 < eps) :
      {i : ι | eps ≤ mu i}.Finite := by
    simpa using hlim.eventually_lt_const heps
  exact ⟨ι, u, v, mu, hp, hsum, hlim, hfin, hK, hC, hAdj⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_cofinite_spectral_decay_kummer

end GegenbauerFock.GeneralUltrasphericalFock
