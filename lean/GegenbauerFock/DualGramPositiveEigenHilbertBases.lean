import GegenbauerFock.CompactGramEigenHilbertBasis

/-!
# V007 — strictly positive multiplicity-indexed Gram eigenvalues

The exact compact self-adjoint Gram spectral constructions now yield
full Hilbert eigenbases, not just dense subspace sums.  For positive
Grams with trivial zero eigenspace, EVERY basis eigenvalue is strictly
positive.  This makes the square-root singular normalization genuine
without excluding a residual kernel by assumption.

The spectral sum identities are retained with precisely the original
unregularized Kummer normalization.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.HilbertSchmidtBasis

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a bounded positive operator has trivial zero eigenspace,
each real eigenvalue associated with a unit Hilbert-basis vector
is strictly positive. This is infinite-dimensional and does not
assume a positive uniform spectral gap. -/
theorem positive_eigenvalue_of_ker_bot
    (T : H →L[ℂ] H)
    (hpos : 0 ≤ T)
    (hzero : eigenspace T.toLinearMap (0 : ℂ) = (⊥ : Submodule ℂ H))
    {ι : Type*} (b : HilbertBasis ι ℂ H) (eig : ι → ℝ)
    (heig : ∀ i : ι, T (b i) = (eig i : ℂ) • b i)
    (i : ι) : 0 < eig i := by
  have hne : b i ≠ 0 := by
    intro hz
    have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
    simp [hz] at hn
  have heigmem : b i ∈ eigenspace T.toLinearMap (eig i : ℂ) := by
    exact (mem_eigenspace_iff).2 (heig i)
  have hhas : HasEigenvalue T.toLinearMap (eig i : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨heigmem, hne⟩
  have hpositive : T.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mp hpos
  have hnonneg : 0 ≤ eig i :=
    eigenvalue_nonneg_of_nonneg hhas
      (fun x => hpositive.re_inner_nonneg_right x)
  have hnotzero : eig i ≠ 0 := by
    intro hi
    have hmem0 : b i ∈ eigenspace T.toLinearMap (0 : ℂ) := by
      rw [mem_eigenspace_iff]
      simpa [hi] using (heig i)
    rw [hzero] at hmem0
    exact hne ((Submodule.mem_bot).mp hmem0)
  exact lt_of_le_of_ne hnonneg hnotzero.symm

#print axioms GegenbauerFock.HilbertSchmidtBasis.positive_eigenvalue_of_ker_bot

end GegenbauerFock.HilbertSchmidtBasis

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true compact source Gram admits a complete eigen-Hilbert basis
of strictly positive eigenvalues whose full multiplicity-counted sum
is the unregularized Kummer normalization. No uniform gap is claimed. -/
theorem exists_sourceGram_positiveEigenHilbertBasis_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (eig : ι → ℝ),
      (∀ i : ι, gram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) ∧
        (∀ i : ι, 0 < eig i) ∧
          Summable eig ∧
            (∑' i : ι, eig i) =
              KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  obtain ⟨ι, b, eig, heig, hs, hsum⟩ :=
    exists_sourceGram_eigenHilbertBasis_kummer lam alpha hlam ha
  have hzero : eigenspace (gram lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    rw [gram_eq_gramIntegralOperator lam alpha hlam ha]
    exact gramIntegralOperator_zero_eigenspace_bot lam alpha hlam ha
  refine ⟨ι, b, eig, heig, ?_, hs, hsum⟩
  intro i
  exact HilbertSchmidtBasis.positive_eigenvalue_of_ker_bot
    (gram lam alpha hlam ha) (gram_nonneg lam alpha hlam ha)
    hzero b eig heig i

/-- The true Fock-output Gram has an independently complete Hilbert
eigenbasis of strictly positive eigenvalues and the SAME total
unregularized Kummer trace, with no surjectivity claim for C. -/
theorem exists_outputGram_positiveEigenHilbertBasis_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (b : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (eig : ι → ℝ),
      (∀ i : ι, outputGram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) ∧
        (∀ i : ι, 0 < eig i) ∧
          Summable eig ∧
            (∑' i : ι, eig i) =
              KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  obtain ⟨ι, b, eig, heig, hs, hsum⟩ :=
    exists_outputGram_eigenHilbertBasis_kummer lam alpha hlam ha
  refine ⟨ι, b, eig, heig, ?_, hs, hsum⟩
  intro i
  exact HilbertSchmidtBasis.positive_eigenvalue_of_ker_bot
    (outputGram lam alpha hlam ha)
    (outputGram_nonneg lam alpha hlam ha)
    (outputGram_zero_eigenspace_bot_unconditional lam alpha hlam ha)
    b eig heig i

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_sourceGram_positiveEigenHilbertBasis_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_outputGram_positiveEigenHilbertBasis_kummer

end GegenbauerFock.GeneralUltrasphericalFock
