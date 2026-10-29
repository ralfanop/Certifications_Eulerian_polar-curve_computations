import GegenbauerFock.CompactGramEigenHilbertBasis
import GegenbauerFock.SingularPairOrthogonality
import GegenbauerFock.SingularPairOutputEigen

/-!
# V007 — unconditional positive singular family with exact Kummer mass

The genuine compact Gegenbauer–Fock operator admits a complete source
Gram Hilbert eigenbasis; injectivity excludes zero eigenvalues. Applying
C/sqrt(mu) produces an orthonormal system of *actual* output vectors,
with both exact singular-pair equations. No global surjectivity of C is
asserted. Target completeness will be treated separately.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every eigenvalue in a complete Hilbert eigenbasis of the actual
injective source Gram is strictly positive, and the family has the
unregularized Kummer sum including spectral multiplicities. -/
theorem exists_positive_sourceGram_eigenHilbertBasis_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      (∀ i, gram lam alpha hlam ha (b i) = (mu i : ℂ) • b i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  obtain ⟨ι, b, mu, heig, hsum, hK⟩ :=
    exists_sourceGram_eigenHilbertBasis_kummer lam alpha hlam ha
  refine ⟨ι, b, mu, ?_, heig, hsum, hK⟩
  intro i
  have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have hnonzero : b i ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hc : C lam alpha hlam ha (b i) ≠ 0 := by
    intro hz
    apply hnonzero
    apply C_injective lam alpha hlam ha
    simpa using hz
  have hnorm : 0 < ‖C lam alpha hlam ha (b i)‖ :=
    norm_pos_iff.mpr hc
  have hsq : ‖C lam alpha hlam ha (b i)‖ ^ 2 = mu i := by
    simpa [hn] using
      (C_gram_real_eigenvector_norm_sq lam alpha hlam ha
        (mu i) (b i) (heig i))
  rw [← hsq]
  exact pow_pos hnorm 2

/-- A genuine orthonormal output singular family from the complete
source eigenbasis. It simultaneously satisfies both singular equations
and carries the exact Kummer squared-singular-value mass. -/
theorem exists_orthonormal_singular_family_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (mu : ι → ℝ) (v : ι → InfiniteAnalysis.FockCoefficients),
      (∀ i, 0 < mu i) ∧
      Orthonormal ℂ v ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (b i) =
        (Real.sqrt (mu i) : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) =
        (Real.sqrt (mu i) : ℂ) • b i) := by
  obtain ⟨ι, b, mu, hp, heig, hsum, hK⟩ :=
    exists_positive_sourceGram_eigenHilbertBasis_kummer lam alpha hlam ha
  let v : ι → InfiniteAnalysis.FockCoefficients :=
    fun i => (Real.sqrt (mu i) : ℂ)⁻¹ • C lam alpha hlam ha (b i)
  have hvnorm : ∀ i, ‖v i‖ = 1 := by
    intro i
    exact C_normalized_singular_target_unit
      lam alpha hlam ha (mu i) (hp i)
      (b i) (b.orthonormal.norm_eq_one i) (heig i)
  have hvortho : ∀ i j : ι, i ≠ j → inner ℂ (v i) (v j) = 0 := by
    intro i j hij
    exact normalized_singular_targets_orthogonal
      lam alpha hlam ha (mu i) (hp i)
      (b i) (b j) (heig i)
      (b.orthonormal.inner_eq_zero hij)
  have hv : Orthonormal ℂ v := ⟨hvnorm, hvortho⟩
  refine ⟨ι, b, mu, v, hp, hv, hsum, hK, ?_, ?_⟩
  · intro i
    exact (C_normalized_singular_pair_right
      lam alpha hlam ha (mu i) (hp i) (b i)).symm
  · intro i
    exact C_normalized_singular_pair_left
      lam alpha hlam ha (mu i) (hp i) (b i) (heig i)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_positive_sourceGram_eigenHilbertBasis_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_orthonormal_singular_family_kummer

end GegenbauerFock.GeneralUltrasphericalFock
