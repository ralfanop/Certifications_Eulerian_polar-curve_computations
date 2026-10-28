import GegenbauerFock.PhyslibPositiveTraceNormTwoSidedSharp
import GegenbauerFock.PhyslibMixedGramTraceClass

/-!
# V007 — sharp bilateral CFC trace norm of the genuine ultraspherical Gram

A specialization of the general positive trace-class two-sided ideal
theorem (separately kernel-audited) to the actual Gegenbauer–Fock
Gram G_{λ,α}=C†C. No direct positive functional calculus on the
concrete L² type is required; its square root is handled abstractly
in the general Hilbert-space theorem.

The right side uses the exact previously certified Kummer value,
not a generic nuclear-mass upper bound.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Optimal bilateral CFC-Schatten bound for arbitrary bounded A,B,
with the exact ultraspherical Kummer mass. -/
theorem gram_twoSided_traceNorm_le_kummer_sharp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
        (A * gram lam alpha hlam ha * B)
        (gram_twoSided_isTraceClass lam alpha hlam ha A B) ≤
      ‖A‖ * ‖B‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    ProbabilisticTheory.traceNorm
        (A * gram lam alpha hlam ha * B)
        (gram_twoSided_isTraceClass lam alpha hlam ha A B) ≤
      ‖A‖ * ‖B‖ *
        ProbabilisticTheory.traceNorm
          (gram lam alpha hlam ha)
          (gram_isTraceClass lam alpha hlam ha) :=
      ProbabilisticTheory.positive_traceNorm_twoSided_le_sharp
        (gram lam alpha hlam ha)
        (gram_nonneg lam alpha hlam ha)
        (gram_isTraceClass lam alpha hlam ha) A B
    _ = ‖A‖ * ‖B‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
      rw [gram_traceNorm_eq_kummer lam alpha hlam ha]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_twoSided_traceNorm_le_kummer_sharp

end GegenbauerFock.GeneralUltrasphericalFock
