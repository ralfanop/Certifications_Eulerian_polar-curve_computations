import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — bilateral singular Fourier expansions for the genuine transform

A complete positive singular Hilbert pair gives norm-convergent
unconditional reconstruction of BOTH original Hilbert spaces and
the exact singular expansions of the genuine C and C† as bounded maps.
All HasSum statements use the genuine infinite-dimensional Hilbert
topology, with no finite truncations or surjectivity of C.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For every positive-parameter Gegenbauer–Fock transform there is
a common multiplicity index with two full Hilbert bases, positive
eigenvalues summing to the genuine Kummer mass, and four norm-convergent
unconditional singular Fourier expansions. -/
theorem exists_complete_singular_fourier_expansions_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        HasSum (fun i : ι => inner ℂ (u i) f • u i) f) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        HasSum (fun i : ι => inner ℂ (v i) F • v i) F) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        HasSum
          (fun i : ι =>
            inner ℂ (u i) f • ((Real.sqrt (mu i) : ℂ) • v i))
          (C lam alpha hlam ha f)) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        HasSum
          (fun i : ι =>
            inner ℂ (v i) F • ((Real.sqrt (mu i) : ℂ) • u i))
          (C_adjoint lam alpha hlam ha F)) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  refine ⟨ι, u, v, mu, hp, hsum, hK, ?_, ?_, ?_, ?_⟩
  · intro f
    simpa only [u.repr_apply_apply] using u.hasSum_repr f
  · intro F
    simpa only [v.repr_apply_apply] using v.hasSum_repr F
  · intro f
    have h := (C lam alpha hlam ha).hasSum (u.hasSum_repr f)
    have hterm :
        (fun i : ι => C lam alpha hlam ha ((u.repr f i) • u i)) =
          (fun i : ι =>
            inner ℂ (u i) f • ((Real.sqrt (mu i) : ℂ) • v i)) := by
      funext i
      rw [map_smul, u.repr_apply_apply, hC i]
    rw [hterm] at h
    exact h
  · intro F
    have h := (C_adjoint lam alpha hlam ha).hasSum (v.hasSum_repr F)
    have hterm :
        (fun i : ι => C_adjoint lam alpha hlam ha ((v.repr F i) • v i)) =
          (fun i : ι =>
            inner ℂ (v i) F • ((Real.sqrt (mu i) : ℂ) • u i)) := by
      funext i
      rw [map_smul, v.repr_apply_apply, hAdj i]
    rw [hterm] at h
    exact h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_fourier_expansions_kummer

end GegenbauerFock.GeneralUltrasphericalFock
