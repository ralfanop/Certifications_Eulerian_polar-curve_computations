import GegenbauerFock.PhyslibDualGramsExplicitKummerResolvent
import GegenbauerFock.PhyslibDualGramsKummerNeumannCorrections

/-!
# V007 — quantitative norm of the exact two-sided inverse correction

For ‖T‖₁<1, the ambient bounded-operator inverse of I−T,
explicitly represented by the true S₁ series of positive powers,
differs from the identity by an operator whose norm is at most
‖T‖₁/(1−‖T‖₁).

Apply separately to the full source and target Grams of the
Gegenbauer–Fock transform. For q=‖z‖·KummerSeries(λ,1/(4α))<1,
the same q/(1−q) bounds both deviations, without identifying
their Hilbert spaces.

The theorem gives a quantitative resolvent-correction estimate,
not an assertion of the maximal domain of invertibility.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm of the *ambient* identity perturbation induced by the
true trace-class geometric correction; no identity inside S₁. -/
theorem positivePowers_ambient_inverse_deviation_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    ‖((1 : H →L[ℂ] H) +
        (∑' n : ℕ, positivePower T n).1) - 1‖ ≤
      ‖T‖ / (1 - ‖T‖) := by
  have hop := operator_norm_le_trace_norm
    (∑' n : ℕ, positivePower T n)
  have hnorm := positivePowers_total_traceNorm_le T hsmall
  simpa only [add_sub_cancel_left] using hop.trans hnorm

#print axioms ProbabilisticTheory.TraceClass.positivePowers_ambient_inverse_deviation_le

end ProbabilisticTheory.TraceClass

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The explicit source-Gram resolvent correction has norm
at most q/(1−q), where q is the exact Gamma–Kummer coupling mass. -/
theorem sourceGram_Kummer_resolvent_deviation_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • gramTraceClass lam alpha hlam ha
    ‖((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) +
      (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n).1) - 1‖ ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) /
      (1 - ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  dsimp
  have hn := scaledGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
  have hc : ‖z • gramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [hn]
    exact hsmall
  simpa only [hn] using
    (ProbabilisticTheory.TraceClass.positivePowers_ambient_inverse_deviation_le
      (z • gramTraceClass lam alpha hlam ha) hc)

/-- The exact same scalar majorant controls the full Fock-output
Gram resolvent correction, within its different Hilbert space. -/
theorem outputGram_Kummer_resolvent_deviation_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    ‖((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) +
      (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n).1) - 1‖ ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) /
      (1 - ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  dsimp
  have hn := scaledOutputGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
  have hc : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [hn]
    exact hsmall
  simpa only [hn] using
    (ProbabilisticTheory.TraceClass.positivePowers_ambient_inverse_deviation_le
      (z • outputGramTraceClass lam alpha hlam ha) hc)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_Kummer_resolvent_deviation_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_Kummer_resolvent_deviation_le

end GegenbauerFock.GeneralUltrasphericalFock
