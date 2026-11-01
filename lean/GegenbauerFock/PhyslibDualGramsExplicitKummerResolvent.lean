import GegenbauerFock.PhyslibTraceClassNeumannAmbientInverse
import GegenbauerFock.PhyslibTraceClassNeumannGeometricBridge
import GegenbauerFock.PhyslibDualGramsKummerAmbientInvertibility

/-!
# V007 — explicit two-sided Gamma–Kummer resolvent formula for both Grams

For T ∈ S₁(H) with ‖T‖₁ < 1, the actual bounded-operator inverse
of I - T is I + S, where S is the genuine S₁ sum of positive
operator powers ∑_(n≥0) T^(n+1). The equality is proved *on both
sides* in the unital ambient B(H), not in the nonunital trace ideal.

The same formula applies separately to z C* C on weighted L² and
z C C* on the coefficient-Fock Hilbert space, when
  ‖z‖ · KummerSeries(λ,1/(4α)) < 1.
No identification of source and output Hilbert spaces is assumed.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual Neumann power series is an explicit two-sided
inverse *correction* in B(H), with the identity only in B(H). -/
theorem positivePowers_ambient_two_sided_inverse
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    (((1 : H →L[ℂ] H) - T.1) *
        (1 + (∑' n : ℕ, positivePower T n).1) = 1) ∧
    (((1 : H →L[ℂ] H) +
        (∑' n : ℕ, positivePower T n).1) * (1 - T.1) = 1) := by
  simpa only [neumannCorrection, neumann_tsum_eq_positivePowers] using
    (neumann_ambient_two_sided_inverse T hsmall)

#print axioms ProbabilisticTheory.TraceClass.positivePowers_ambient_two_sided_inverse

end ProbabilisticTheory.TraceClass

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Exact two-sided resolvent correction for the full weighted-L²
Gram C* C, under the explicit Gamma–Kummer trace radius test. -/
theorem sourceGram_explicit_Kummer_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • gramTraceClass lam alpha hlam ha
    let S := ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n
    (((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) - T.1) * (1 + S.1) = 1) ∧
    (((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) + S.1) * (1 - T.1) = 1) := by
  dsimp
  have hc : ‖z • gramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [scaledGramTraceClass_actual_norm_eq_kummer]
    exact hsmall
  exact ProbabilisticTheory.TraceClass.positivePowers_ambient_two_sided_inverse
    (z • gramTraceClass lam alpha hlam ha) hc

/-- Exact two-sided resolvent correction for the full coefficient-Fock
Gram C C*, with the same Gamma–Kummer scalar criterion but on
its own different target Hilbert space. -/
theorem outputGram_explicit_Kummer_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    let S := ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n
    (((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) - T.1) * (1 + S.1) = 1) ∧
    (((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) + S.1) * (1 - T.1) = 1) := by
  dsimp
  have hc : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [scaledOutputGramTraceClass_actual_norm_eq_kummer]
    exact hsmall
  exact ProbabilisticTheory.TraceClass.positivePowers_ambient_two_sided_inverse
    (z • outputGramTraceClass lam alpha hlam ha) hc

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_explicit_Kummer_resolvent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_explicit_Kummer_resolvent

end GegenbauerFock.GeneralUltrasphericalFock
