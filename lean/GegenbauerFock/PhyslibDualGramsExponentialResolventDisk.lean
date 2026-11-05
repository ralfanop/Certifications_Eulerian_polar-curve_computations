import GegenbauerFock.PhyslibDualGramsKummerAmbientInvertibility
import GegenbauerFock.KummerPositiveBounds

/-!
# V007 — an explicit exponential resolvent region for both CFC Grams

For every λ>0 and α>0, both source G=C†C and output \widetilde G=CC†
are genuine Schatten S₁ elements with identical Kummer mass K.
The certified scalar bound K(λ,1/(4α))≤exp(1/(4α))
implies that the *same λ-independent sufficient condition*

    ‖z‖ * exp(1/(4α)) < 1

ensures invertibility of 1-zG and 1-z\widetilde G, each in its
own bounded-operator algebra. This does not assert optimality of the
resolvent disk or identify the underlying Hilbert spaces.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- A parameter-only explicit sufficient disk for simultaneous
ambient invertibility of both positive CFC trace-class Grams. -/
theorem dualGrams_ambient_one_sub_isUnit_exponential
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall : ‖z‖ * Real.exp (1 / (4 * alpha)) < 1) :
    IsUnit ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) -
      (z • gramTraceClass lam alpha hlam ha).1) ∧
    IsUnit ((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) -
      (z • outputGramTraceClass lam alpha hlam ha).1) := by
  have hz : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hK : KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ≤
      Real.exp (1 / (4 * alpha)) :=
    KummerCoefficients.kummerSeries_le_exp
      lam (1 / (4 * alpha)) hlam hz
  have hs : ‖z‖ * KummerCoefficients.kummerSeries lam
      (1 / (4 * alpha)) < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hK (norm_nonneg z)) hsmall
  exact dualGrams_ambient_one_sub_isUnit_Kummer
    lam alpha hlam ha z hs

#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_ambient_one_sub_isUnit_exponential

end GegenbauerFock.GeneralUltrasphericalFock
