import GegenbauerFock.DualGramPositiveTraceDiagonal

/-!
# V007 — real eigenbasis trace summability for the genuine dual Grams

For any full Hilbert eigenbasis of the positive ultraspherical source Gram
or the positive Fock-output Gram, the real eigenvalue family is summable
and its sum equals the SAME unregularized Kummer expression.

The chosen bases and their eigen-equations are explicit hypotheses.
This module does NOT postulate or construct a global eigenbasis; that
separate existence/enumeration proof must use compact spectral theory.
No finite-rank surrogate and no changed normalization is involved.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

private theorem eigenbasis_inner_real_eq
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H)
    (T : H →L[ℂ] H) (eig : w → ℝ)
    (heig : ∀ i : w, T (b i) = (eig i : ℂ) • b i) (i : w) :
    (inner ℂ (b i) (T (b i))).re = eig i := by
  rw [heig i, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  simp [hn]

/-- Every complete orthonormal source-Gram eigenbasis has a summable
real eigenvalue family, with multiplicities encoded by its index set. -/
theorem sourceGram_realEigenvalues_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Set (Lp ℂ 2 (Ultraspherical.measure lam))}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (eig : w → ℝ)
    (heig : ∀ i : w,
      gram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) :
    Summable eig := by
  exact (sourceGram_diagonal_summable lam alpha hlam ha b).congr
    (eigenbasis_inner_real_eq b (gram lam alpha hlam ha) eig heig)

/-- In a full source Gram eigenbasis the sum of all eigenvalues,
counted with their eigenspace multiplicities, equals the Kummer mass. -/
theorem sourceGram_realEigenvalues_tsum_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Set (Lp ℂ 2 (Ultraspherical.measure lam))}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (eig : w → ℝ)
    (heig : ∀ i : w,
      gram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) :
    (∑' i : w, eig i) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : w, eig i) =
        ∑' i : w,
          (inner ℂ (b i) (gram lam alpha hlam ha (b i))).re := by
      apply tsum_congr
      intro i
      exact (eigenbasis_inner_real_eq b
        (gram lam alpha hlam ha) eig heig i).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      sourceGram_diagonal_tsum_eq_kummer lam alpha hlam ha b

/-- Every complete Fock-output Gram eigenbasis also has a summable
real eigenvalue family, independently of the source Gram basis. -/
theorem outputGram_realEigenvalues_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Set InfiniteAnalysis.FockCoefficients}
    (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients)
    (eig : w → ℝ)
    (heig : ∀ i : w,
      outputGram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) :
    Summable eig := by
  exact (outputGram_diagonal_summable lam alpha hlam ha b).congr
    (eigenbasis_inner_real_eq b (outputGram lam alpha hlam ha) eig heig)

/-- In a full Fock-output Gram eigenbasis the eigenvalue sum has
exactly the same true trace and unregularized Kummer normalization. -/
theorem outputGram_realEigenvalues_tsum_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Set InfiniteAnalysis.FockCoefficients}
    (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients)
    (eig : w → ℝ)
    (heig : ∀ i : w,
      outputGram lam alpha hlam ha (b i) = (eig i : ℂ) • b i) :
    (∑' i : w, eig i) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : w, eig i) =
        ∑' i : w,
          (inner ℂ (b i) (outputGram lam alpha hlam ha (b i))).re := by
      apply tsum_congr
      intro i
      exact (eigenbasis_inner_real_eq b
        (outputGram lam alpha hlam ha) eig heig i).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      outputGram_diagonal_tsum_eq_kummer lam alpha hlam ha b

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_realEigenvalues_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_realEigenvalues_tsum_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_realEigenvalues_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_realEigenvalues_tsum_eq_kummer

end GegenbauerFock.GeneralUltrasphericalFock
