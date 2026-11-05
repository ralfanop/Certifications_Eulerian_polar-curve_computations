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
  have hT : HilbertSchmidtBasis.IsHS T :=
    HilbertSchmidtBasis.isHS_comp_left
      (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha) A
  let hSrc : ProbabilisticTheory.IsTraceClass (T.adjoint.comp T) :=
    ProbabilisticTheory.isTraceClass_adjoint_comp_self_of_isHS T hT
  let hDst : ProbabilisticTheory.IsTraceClass (T.comp T.adjoint) :=
    outputGramAfterLeft_isTraceClass lam alpha hlam ha A
  have hSrcSum : Summable (fun i : hSrc.choose =>
      ‖T (hSrc.choose_spec.choose i)‖ ^ 2) :=
    hT hSrc.choose_spec.choose
  have hGrams :
      ProbabilisticTheory.traceNorm (T.comp T.adjoint) hDst =
        ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc :=
    (HilbertSchmidtBasis.traceNorm_adjoint_comp_eq_comp_adjoint
      T hT hSrc hDst).symm
  have hSource :
      ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc =
        ∑' i : hSrc.choose, ‖T (hSrc.choose_spec.choose i)‖ ^ 2 :=
    ProbabilisticTheory.traceNorm_adjoint_comp_self_eq_witness_energy T hT
  change ProbabilisticTheory.traceNorm (T.comp T.adjoint) hDst =
    ∑' j : w, ‖T.adjoint (b j)‖ ^ 2
  calc
    ProbabilisticTheory.traceNorm (T.comp T.adjoint) hDst =
        ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc := hGrams
    _ = ∑' i : hSrc.choose,
          ‖T (hSrc.choose_spec.choose i)‖ ^ 2 := hSource
    _ = ∑' j : w, ‖T.adjoint (b j)‖ ^ 2 :=
      (HilbertSchmidtBasis.hasSum_adjoint_energy_rectangular
        T hSrc.choose_spec.choose b hSrcSum).tsum_eq.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_adjoint_basisEnergy_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_traceNorm_eq_adjoint_basisEnergy

end GegenbauerFock.GeneralUltrasphericalFock
