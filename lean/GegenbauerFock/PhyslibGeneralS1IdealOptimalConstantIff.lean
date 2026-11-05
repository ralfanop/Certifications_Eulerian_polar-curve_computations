import GegenbauerFock.PhyslibGeneralS1IdealSharpnessWitness

/-!
# V007 — exact admissible constants for the genuine CFC Schatten S₁ ideal

On the actual ultraspherical complex Hilbert space, a proposed
uniform bilateral S₁ trace-norm estimate with scalar coefficient c
holds for every trace-class T and every bounded A,B **if and only if**
1 ≤ c. This unifies the separately kernel-certified upper inequality
and the strictly optimal coefficient-one counterexample for c<1.

Unlike the underlying lower-bound witness, the theorem quantifies
over ALL (including nonpositive, nonnormal) CFC trace-class operators.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Characterization of every valid universal real coefficient in
the nonpositive trace-class two-sided ideal bound on ultraspherical L². -/
theorem general_S1_ideal_bound_iff_coefficient_ge_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℝ) :
    (∀ (T A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
      (hT : ProbabilisticTheory.IsTraceClass T),
        ProbabilisticTheory.traceNorm (A * T * B)
          (ProbabilisticTheory.isTraceClass_twoSided T hT A B) ≤
        c * (‖A‖ * ‖B‖ * ProbabilisticTheory.traceNorm T hT)) ↔
      1 ≤ c := by
  constructor
  · intro hall
    by_contra hnot
    have hc : c < 1 := lt_of_not_ge hnot
    exact (general_S1_ideal_coefficient_one_optimal lam alpha hlam ha c hc) hall
  · intro hc
    intro T A B hT
    have hK : 0 ≤ ‖A‖ * ‖B‖ *
        ProbabilisticTheory.traceNorm T hT :=
      mul_nonneg
        (mul_nonneg (norm_nonneg A) (norm_nonneg B))
        (ProbabilisticTheory.traceNorm_nonneg T hT)
    calc
      ProbabilisticTheory.traceNorm (A * T * B)
          (ProbabilisticTheory.isTraceClass_twoSided T hT A B) ≤
          ‖A‖ * ‖B‖ * ProbabilisticTheory.traceNorm T hT :=
        ProbabilisticTheory.traceNorm_twoSided_le T A B hT
      _ = (1 : ℝ) * (‖A‖ * ‖B‖ *
          ProbabilisticTheory.traceNorm T hT) := by ring
      _ ≤ c * (‖A‖ * ‖B‖ *
          ProbabilisticTheory.traceNorm T hT) :=
        mul_le_mul_of_nonneg_right hc hK

#print axioms GegenbauerFock.GeneralUltrasphericalFock.general_S1_ideal_bound_iff_coefficient_ge_one

end GegenbauerFock.GeneralUltrasphericalFock
