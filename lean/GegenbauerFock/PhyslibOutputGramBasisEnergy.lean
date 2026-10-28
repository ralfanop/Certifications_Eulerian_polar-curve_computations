import GegenbauerFock.PhyslibOutputGramConjugationBound
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — exact postprocessed Fock-output Gram trace on every Hilbert basis

The preceding module proves the sharp conjugation trace-ideal bound
  ‖A(CC†)A†‖₁ ≤ ‖A‖² ‖CC†‖₁.
Here we strengthen the identity behind that inequality: for EVERY
complete Hilbert basis e_j of the genuine infinite-dimensional Fock
coefficient Hilbert space,

  ‖A(CC†)A†‖₁ = ∑_j ‖C† A† e_j‖².

The trace norm is the true basis-independent CFC absolute trace, not a
surrogate nuclear mass or finite-rank truncation. This does not assume
the still-separate general S₁ triangle inequality or Banach completion.

This module is a candidate until exact-SHA CI with #print axioms passes.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

private theorem outputBasis_re_inner_swap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- The squared norm of the actual postprocessed adjoint is
summable on ANY complete Fock output Hilbert basis. -/
theorem outputGramAfterLeft_adjoint_basisEnergy_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients)
    {w : Type} (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients) :
    Summable (fun j : w =>
      ‖(A.comp (C lam alpha hlam ha)).adjoint (b j)‖ ^ 2) := by
  have hT : HilbertSchmidtBasis.IsHS (A.comp (C lam alpha hlam ha)) :=
    HilbertSchmidtBasis.isHS_comp_left
      (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha) A
  exact (HilbertSchmidtBasis.isHS_adjoint_rectangular
    (A.comp (C lam alpha hlam ha)) hT) b

/-- Exact formula for the genuine CFC trace norm of A(CC†)A†,
evaluated on an arbitrary Fock Hilbert basis. -/
theorem outputGramAfterLeft_traceNorm_eq_adjoint_basisEnergy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients)
    {w : Set InfiniteAnalysis.FockCoefficients}
    (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients) :
    ProbabilisticTheory.traceNorm
        (outputGramAfterLeft lam alpha hlam ha A)
        (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) =
      ∑' j : w,
        ‖(A.comp (C lam alpha hlam ha)).adjoint (b j)‖ ^ 2 := by
  let T := A.comp (C lam alpha hlam ha)
  have hpos : 0 ≤ outputGramAfterLeft lam alpha hlam ha A := by
    change 0 ≤ T.comp T.adjoint
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      ((ContinuousLinearMap.nonneg_iff_isPositive).2
        (ContinuousLinearMap.isPositive_adjoint_comp_self T.adjoint))
  calc
    ProbabilisticTheory.traceNorm
        (outputGramAfterLeft lam alpha hlam ha A)
        (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) =
      ∑' j : w, (inner ℂ (b j)
        (CFC.abs (outputGramAfterLeft lam alpha hlam ha A) (b j))).re :=
          ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
            (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) b
    _ = ∑' j : w, (inner ℂ (b j)
          (outputGramAfterLeft lam alpha hlam ha A (b j))).re := by
            have hAbs :
                CFC.abs (outputGramAfterLeft lam alpha hlam ha A) =
                  outputGramAfterLeft lam alpha hlam ha A :=
              CFC.abs_of_nonneg _ hpos
            apply tsum_congr
            intro j
            exact congrArg (fun (K : InfiniteAnalysis.FockCoefficients →L[ℂ]
              InfiniteAnalysis.FockCoefficients) =>
                (inner ℂ (b j) (K (b j))).re) hAbs
    _ = ∑' j : w, ‖T.adjoint (b j)‖ ^ 2 := by
      apply tsum_congr
      intro j
      have hnorm :
          ‖T.adjoint (b j)‖ ^ 2 =
            (inner ℂ
              (outputGramAfterLeft lam alpha hlam ha A (b j)) (b j)).re := by
        simpa only [outputGramAfterLeft, HilbertGram.gram,
          ContinuousLinearMap.adjoint_adjoint, RCLike.re_eq_complex_re] using
          (HilbertGram.gram_norm_sq T.adjoint (b j))
      exact (outputBasis_re_inner_swap (b j)
        (outputGramAfterLeft lam alpha hlam ha A (b j))).trans hnorm.symm
    _ = ∑' j : w,
          ‖(A.comp (C lam alpha hlam ha)).adjoint (b j)‖ ^ 2 := rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_adjoint_basisEnergy_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_traceNorm_eq_adjoint_basisEnergy

end GegenbauerFock.GeneralUltrasphericalFock
