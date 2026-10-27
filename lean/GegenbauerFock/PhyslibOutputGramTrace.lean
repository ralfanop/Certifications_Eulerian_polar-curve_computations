import GegenbauerFock.RectangularHSGramTraceEquality
import GegenbauerFock.GramSingularTransfer

/-!
# V007 — actual Fock-output Gram belongs to both Schatten ideals

Apply the general rectangular Hilbert–Schmidt adjoint theorem and
the equality of genuine CFC trace norms to the nontruncated
Gegenbauer–Fock transform C : L²(νλ) → ℓ².

The *output* Gram CC† is trace class and Hilbert–Schmidt, and has
the same precisely Gamma-normalized Kummer trace norm as the
previously certified *source* Gram C†C.

This is an independent bridge on the output Hilbert space, not
a finite-dimensional surrogate. The files imported above and this
new application require exact-SHA CI and axiom audit prior to
any claim of Lean certification.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- For every λ,α>0 the genuine infinite-dimensional Fock-output
Gram CC† lies in both Physlib-compatible S₁ and S₂. -/
theorem outputGram_inPhyslibS1_and_S2
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.IsTraceClass (outputGram lam alpha hlam ha) ∧
    ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      (outputGram lam alpha hlam ha) := by
  change
    ProbabilisticTheory.IsTraceClass
      ((C lam alpha hlam ha).comp (C lam alpha hlam ha).adjoint) ∧
    ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      ((C lam alpha hlam ha).comp (C lam alpha hlam ha).adjoint)
  exact (HilbertSchmidtBasis.bothGrams_in_S1_and_S2
    (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha)).2

/-- In particular, the Fock-output Gram is truly CFC trace class. -/
theorem outputGram_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.IsTraceClass (outputGram lam alpha hlam ha) :=
  (outputGram_inPhyslibS1_and_S2 lam alpha hlam ha).1

/-- The genuine output-side trace norm has *the same* exact
unregularized hypergeometric value as the source-side Gram.
No equality of formal nuclear witnesses is substituted. -/
theorem outputGram_traceNorm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm (outputGram lam alpha hlam ha)
      (outputGram_isTraceClass lam alpha hlam ha) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  have hEq :
      ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
        (gram_isTraceClass lam alpha hlam ha) =
      ProbabilisticTheory.traceNorm (outputGram lam alpha hlam ha)
        (outputGram_isTraceClass lam alpha hlam ha) :=
    HilbertSchmidtBasis.traceNorm_adjoint_comp_eq_comp_adjoint
      (C lam alpha hlam ha)
      (C_isHilbertSchmidt lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha)
      (outputGram_isTraceClass lam alpha hlam ha)
  exact hEq.symm.trans (gram_traceNorm_eq_kummer lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_inPhyslibS1_and_S2
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_isTraceClass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_traceNorm_eq_kummer

end GegenbauerFock.GeneralUltrasphericalFock
