import GegenbauerFock.PhyslibOutputGramTrace

/-!
# V007 — sharp output-side positive trace-ideal conjugation bound

For the genuine Gegenbauer--Fock analysis operator
  C_{λ,α} : L²(ν_λ) → ℓ²
and *any* bounded operator A on the complete Fock coefficient space,
its output Gram after postprocessing is
  (A C)(A C)† = A(CC†)A†.
The operator is genuinely positive and CFC trace class, and its true
Physlib-compatible trace norm satisfies
  ‖A(CC†)A†‖₁ ≤ ‖A‖² · Γ(λ+1) ₁F₁(1/2;λ+1;1/(4α)).

The argument relies on already verified rectangular S₂→S₁ Gram
membership, equality of both Gram trace norms, and the full,
basis-independent Kummer energy identity. It does NOT assume the
unverified general S₁ Banach norm inequality.

This standalone module is a new candidate until pinned Lean CI passes
and its printed axioms are audited. No new axioms or sorry.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Output Gram of the bounded postprocessed Gegenbauer--Fock map A ∘ C. -/
noncomputable def outputGramAfterLeft
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients :=
  ((A.comp (C lam alpha hlam ha)).comp
    (A.comp (C lam alpha hlam ha)).adjoint)

/-- Exact bounded conjugation identity on the original Fock output Gram. -/
theorem outputGramAfterLeft_eq_conjugated
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    outputGramAfterLeft lam alpha hlam ha A =
      A.comp ((outputGram lam alpha hlam ha).comp A.adjoint) := by
  unfold outputGramAfterLeft outputGram C_adjoint
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The Fock output Gram remains in *both* real CFC-based Schatten
predicates after arbitrary bounded output postprocessing. -/
theorem outputGramAfterLeft_inPhyslibS1_and_S2
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    ProbabilisticTheory.IsTraceClass (outputGramAfterLeft lam alpha hlam ha A) ∧
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
        (outputGramAfterLeft lam alpha hlam ha A) := by
  let T := A.comp (C lam alpha hlam ha)
  have hT : HilbertSchmidtBasis.IsHS T :=
    HilbertSchmidtBasis.isHS_comp_left
      (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha) A
  change
    ProbabilisticTheory.IsTraceClass (T.comp T.adjoint) ∧
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
        (T.comp T.adjoint)
  exact (HilbertSchmidtBasis.bothGrams_in_S1_and_S2 T hT).2

/-- Actual CFC-absolute trace-class membership of A(CC†)A†. -/
theorem outputGramAfterLeft_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    ProbabilisticTheory.IsTraceClass (outputGramAfterLeft lam alpha hlam ha A) :=
  (outputGramAfterLeft_inPhyslibS1_and_S2 lam alpha hlam ha A).1

/-- The genuine CFC output-Gram trace norm satisfies the sharp
postprocessing bound, without invoking any unported generic S₁ norm API. -/
theorem outputGramAfterLeft_traceNorm_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    ProbabilisticTheory.traceNorm
        (outputGramAfterLeft lam alpha hlam ha A)
        (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) ≤
      ‖A‖ ^ 2 * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  let T := A.comp (C lam alpha hlam ha)
  have hT : HilbertSchmidtBasis.IsHS T :=
    HilbertSchmidtBasis.isHS_comp_left
      (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha) A
  let hSrc : ProbabilisticTheory.IsTraceClass (T.adjoint.comp T) :=
    ProbabilisticTheory.isTraceClass_adjoint_comp_self_of_isHS T hT
  let hDst : ProbabilisticTheory.IsTraceClass (T.comp T.adjoint) :=
    outputGramAfterLeft_isTraceClass lam alpha hlam ha A
  have hpositive : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hEq :
      ProbabilisticTheory.traceNorm
          (outputGramAfterLeft lam alpha hlam ha A)
          (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) =
        ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc := by
    exact (HilbertSchmidtBasis.traceNorm_adjoint_comp_eq_comp_adjoint
      T hT hSrc hDst).symm
  have hbound (i : hSrc.choose) :
      ‖T (hSrc.choose_spec.choose i)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖ ^ 2 := by
    change ‖A (C lam alpha hlam ha (hSrc.choose_spec.choose i))‖ ^ 2 ≤ _
    calc
      ‖A (C lam alpha hlam ha (hSrc.choose_spec.choose i))‖ ^ 2 ≤
          (‖A‖ * ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖) ^ 2 := by
            gcongr
            exact ContinuousLinearMap.le_opNorm A
              (C lam alpha hlam ha (hSrc.choose_spec.choose i))
      _ = ‖A‖ ^ 2 * ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖ ^ 2 := by
            ring
  have hsC : Summable (fun i : hSrc.choose =>
      ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖ ^ 2) :=
    C_isHilbertSchmidt lam alpha hlam ha hSrc.choose_spec.choose
  calc
    ProbabilisticTheory.traceNorm
        (outputGramAfterLeft lam alpha hlam ha A)
        (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) =
      ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc := hEq
    _ = ∑' i : hSrc.choose,
        (inner ℂ (hSrc.choose_spec.choose i)
          ((T.adjoint.comp T) (hSrc.choose_spec.choose i))).re := by
          exact ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
            (T.adjoint.comp T) hpositive hSrc
    _ = ∑' i : hSrc.choose, ‖T (hSrc.choose_spec.choose i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          have hn := HilbertGram.gram_norm_sq T (hSrc.choose_spec.choose i)
          have hnormal :
              ‖T (hSrc.choose_spec.choose i)‖ ^ 2 =
                (inner ℂ ((T.adjoint.comp T) (hSrc.choose_spec.choose i))
                  (hSrc.choose_spec.choose i)).re := by
            simpa only [HilbertGram.gram, RCLike.re_eq_complex_re] using hn
          calc
            (inner ℂ (hSrc.choose_spec.choose i)
              ((T.adjoint.comp T) (hSrc.choose_spec.choose i))).re =
              (inner ℂ ((T.adjoint.comp T) (hSrc.choose_spec.choose i))
                (hSrc.choose_spec.choose i)).re := by
                  rw [← Complex.conj_re
                    (inner ℂ ((T.adjoint.comp T) (hSrc.choose_spec.choose i))
                      (hSrc.choose_spec.choose i))]
                  congr 1
                  exact (inner_conj_symm (𝕜 := ℂ)
                    (hSrc.choose_spec.choose i)
                    ((T.adjoint.comp T) (hSrc.choose_spec.choose i)))
            _ = ‖T (hSrc.choose_spec.choose i)‖ ^ 2 := hnormal.symm
    _ ≤ ∑' i : hSrc.choose,
          ‖A‖ ^ 2 * ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖ ^ 2 := by
            exact (hT hSrc.choose_spec.choose).tsum_le_tsum hbound
              (hsC.mul_left (‖A‖ ^ 2))
    _ = ‖A‖ ^ 2 *
          (∑' i : hSrc.choose,
            ‖C lam alpha hlam ha (hSrc.choose_spec.choose i)‖ ^ 2) := tsum_mul_left
    _ = ‖A‖ ^ 2 *
          KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
            rw [C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha
              hSrc.choose_spec.choose]

/-- The same norm bound expressed entirely in actual CFC S₁ norms. -/
theorem outputGramAfterLeft_traceNorm_le_outputGram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    ProbabilisticTheory.traceNorm
        (outputGramAfterLeft lam alpha hlam ha A)
        (outputGramAfterLeft_isTraceClass lam alpha hlam ha A) ≤
      ‖A‖ ^ 2 *
        ProbabilisticTheory.traceNorm
          (outputGram lam alpha hlam ha)
          (outputGram_isTraceClass lam alpha hlam ha) := by
  rw [outputGram_traceNorm_eq_kummer lam alpha hlam ha]
  exact outputGramAfterLeft_traceNorm_le_kummer lam alpha hlam ha A

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_eq_conjugated
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_inPhyslibS1_and_S2
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_traceNorm_le_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramAfterLeft_traceNorm_le_outputGram

end GegenbauerFock.GeneralUltrasphericalFock
