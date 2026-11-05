import GegenbauerFock.PositivePolarAmplitude

/-!
# V007 — full unitary polar adjoint formula and output Gram factorization

For the actual Gegenbauer–Fock map C = W P with a proven unitary W
and positive self-adjoint bounded P, the ACTUAL Hilbert adjoint
satisfies C† = P ∘ W⁻¹ on the entire Fock coefficient Hilbert space.
Consequently the genuine output Gram is W ∘ P² ∘ W⁻¹.
The proof is by equality of Hilbert-basis coefficients and preservation
of inner products under W, not by postulating an adjoint formula.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The exact positive-polar operator gives both the genuine
adjoint formula and the output Gram conjugacy, over full Hilbert
spaces with the common strictly-positive Kummer-summable family. -/
theorem exists_full_unitary_polar_adjoint_and_outputGram_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) ∧
      P.adjoint = P ∧
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsPositive ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        C_adjoint lam alpha hlam ha F = P (W.symm F)) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        outputGram lam alpha hlam ha F =
          W (P (P (W.symm F)))) := by
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hinj, hself, hPos⟩ :=
    exists_positive_polar_amplitude_kummer lam alpha hlam ha
  have hAdj (F : InfiniteAnalysis.FockCoefficients) :
      C_adjoint lam alpha hlam ha F = P (W.symm F) := by
    apply u.repr.injective
    ext i
    rw [u.repr_apply_apply, u.repr_apply_apply]
    calc
      inner ℂ (u i) (C_adjoint lam alpha hlam ha F) =
          inner ℂ (C lam alpha hlam ha (u i)) F :=
            (C lam alpha hlam ha).adjoint_inner_right (u i) F
      _ = inner ℂ (W (P (u i))) F := by rw [hC (u i)]
      _ = inner ℂ (P (u i)) (W.symm F) := by
        calc
          inner ℂ (W (P (u i))) F =
              inner ℂ (W (P (u i))) (W (W.symm F)) := by
                rw [W.apply_symm_apply]
          _ = inner ℂ (P (u i)) (W.symm F) :=
            W.inner_map_map (P (u i)) (W.symm F)
      _ = inner ℂ (u i) (P (W.symm F)) := by
        calc
          inner ℂ (P (u i)) (W.symm F) =
              inner ℂ (u i) (P.adjoint (W.symm F)) :=
                (P.adjoint_inner_right (u i) (W.symm F)).symm
          _ = inner ℂ (u i) (P (W.symm F)) := by rw [hself]
  have hOut (F : InfiniteAnalysis.FockCoefficients) :
      outputGram lam alpha hlam ha F =
        W (P (P (W.symm F))) := by
    change C lam alpha hlam ha (C_adjoint lam alpha hlam ha F) =
      W (P (P (W.symm F)))
    rw [hAdj F, hC (P (W.symm F))]
  exact ⟨ι, u, mu, W, P, hp, hsum, hK, hC, hP2,
    hself, hPos, hAdj, hOut⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_full_unitary_polar_adjoint_and_outputGram_kummer

end GegenbauerFock.GeneralUltrasphericalFock
