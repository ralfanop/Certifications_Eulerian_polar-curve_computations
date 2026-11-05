import GegenbauerFock.PhyslibDualGramsSimultaneousGeometricKummer
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# V007 — Gamma-Kummer criterion for ambient invertibility of both Grams

For λ,α>0 let K = KummerSeries λ (1/(4α)).
The genuine trace-class norm of BOTH the weighted-L² Gram C* C
and the coefficient-Fock Gram C C* equals K.

Thus ‖z‖·K < 1 gives ‖(zG : S₁).operator‖op < 1 on each
corresponding (distinct) Hilbert space. The actual unital ambient
operator (1 - zG) is therefore invertible there, by Mathlib's
normed-ring geometric inverse theorem. No unit is introduced in S₁;
the identity exists only in the encompassing bounded-operator algebra.

This criterion is sufficient, not a claim of the exact spectral
radius or maximal resolvent domain.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- The full source Gram has a genuine ambient bounded-operator
inverse under the *exact trace-norm* Gamma-Kummer smallness test. -/
theorem sourceGram_ambient_one_sub_isUnit_Kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsUnit ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) -
      (z • gramTraceClass lam alpha hlam ha).1) := by
  have htrace : ‖z • gramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [scaledGramTraceClass_actual_norm_eq_kummer]
    exact hsmall
  have hop := lt_of_le_of_lt
    (ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm
      (z • gramTraceClass lam alpha hlam ha)) htrace
  exact isUnit_one_sub_of_norm_lt_one hop

/-- The full Fock-output Gram has a genuine ambient inverse on
its own coefficient Hilbert space, with the same Kummer criterion. -/
theorem outputGram_ambient_one_sub_isUnit_Kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsUnit ((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) -
      (z • outputGramTraceClass lam alpha hlam ha).1) := by
  have htrace : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [scaledOutputGramTraceClass_actual_norm_eq_kummer]
    exact hsmall
  have hop := lt_of_le_of_lt
    (ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm
      (z • outputGramTraceClass lam alpha hlam ha)) htrace
  exact isUnit_one_sub_of_norm_lt_one hop

/-- One scalar Gamma-Kummer condition certifies the two *different*
ambient invertibilities in the respective unital operator algebras. -/
theorem dualGrams_ambient_one_sub_isUnit_Kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsUnit ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) -
      (z • gramTraceClass lam alpha hlam ha).1) ∧
    IsUnit ((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) -
      (z • outputGramTraceClass lam alpha hlam ha).1) :=
  ⟨sourceGram_ambient_one_sub_isUnit_Kummer lam alpha hlam ha z hsmall,
   outputGram_ambient_one_sub_isUnit_Kummer lam alpha hlam ha z hsmall⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_ambient_one_sub_isUnit_Kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_ambient_one_sub_isUnit_Kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_ambient_one_sub_isUnit_Kummer

end GegenbauerFock.GeneralUltrasphericalFock
