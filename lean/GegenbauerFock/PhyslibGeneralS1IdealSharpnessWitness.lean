import GegenbauerFock.PhyslibTraceClassIdealNormSharp
import GegenbauerFock.PhyslibGramBilateralSharpnessWitness

/-!
# V007 — sharpness of the general nonpositive CFC Schatten S₁ ideal law

The generic genuine CFC-S₁ inequality for arbitrary trace-class T
and bounded multipliers A,B is already independently kernel-certified.

To prove that its universal coefficient one is *necessary*, not just
sufficient, specialize the hypothetical improved inequality to the
nonzero positive ultraspherical Gram G_{λ,α}.  The previously
kernel-certified exact Kummer trace and sharpness witness then rule
out every c<1.  This proves a global no-improvement statement for
*arbitrary trace-class T*, rather than only a fixed positive Gram.

The demonstration uses neither finite-rank surrogate operators nor
a nontrivial-space typeclass assumption or additional axioms.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- For each ultraspherical source space, no coefficient less than one
can bound the genuine CFC trace norm of A*T*B uniformly over *all*
trace-class T and all bounded A,B.

The nonpositive Schatten S₁ ideal inequality is therefore sharp. -/
theorem general_S1_ideal_coefficient_one_optimal
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℝ) (hc : c < 1) :
    ¬ ∀ (T A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
      (hT : ProbabilisticTheory.IsTraceClass T),
        ProbabilisticTheory.traceNorm (A * T * B)
          (ProbabilisticTheory.isTraceClass_twoSided T hT A B) ≤
        c * (‖A‖ * ‖B‖ * ProbabilisticTheory.traceNorm T hT) := by
  intro hall
  apply gram_bilateral_coefficient_one_optimal lam alpha hlam ha c hc
  intro A B
  have h := hall (gram lam alpha hlam ha) A B
    (gram_isTraceClass lam alpha hlam ha)
  change ProbabilisticTheory.traceNorm
      (A * gram lam alpha hlam ha * B)
      (gram_twoSided_isTraceClass lam alpha hlam ha A B) ≤
    c * (‖A‖ * ‖B‖ *
      ProbabilisticTheory.traceNorm
        (gram lam alpha hlam ha) (gram_isTraceClass lam alpha hlam ha)) at h
  rw [gram_traceNorm_eq_kummer lam alpha hlam ha] at h
  exact h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.general_S1_ideal_coefficient_one_optimal

end GegenbauerFock.GeneralUltrasphericalFock
