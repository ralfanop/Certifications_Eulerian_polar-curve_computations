import GegenbauerFock.PhyslibGramScaledGeometricKummer
import GegenbauerFock.PhyslibOutputGramScaledGeometricKummer

/-!
# V007 — uniform Gamma–Kummer geometric error for both Fock Grams

The source Gram C†C and target Gram CC† act on *different* Hilbert
spaces. Nonetheless their true CFC S₁ trace norms have the same
Kummer mass. Therefore a single complex coupling condition
‖z‖ * KummerSeries(λ, 1/(4α)) < 1 gives the same quantitative
nonunital geometric-series remainder for both, simultaneously.

The max of the two trace-norm errors, and separately the max
of the two bounded-operator errors, is bounded by the identical
explicit scalar. No identification of Hilbert spaces is implied.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The Kummer radius condition is identical for the source Gram
and for the Fock coefficient output Gram. -/
theorem scaled_dualGrams_traceNorm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) :
    ‖z • gramTraceClass lam alpha hlam ha‖ =
      ‖z • outputGramTraceClass lam alpha hlam ha‖ := by
  rw [scaledGramTraceClass_actual_norm_eq_kummer,
    scaledOutputGramTraceClass_actual_norm_eq_kummer]

/-- A *single* Kummer geometric majorant bounds the larger of
the two true S₁ truncation errors on distinct Hilbert spaces. -/
theorem dualGrams_simultaneous_traceNorm_geometric_error_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    max
      (ProbabilisticTheory.TraceClass.traceNorm _
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) -
         (∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n)))
      (ProbabilisticTheory.TraceClass.traceNorm _
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) -
         (∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n))) ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  apply max_le
  · exact scaledGram_positivePowers_traceNorm_error_le_kummer
      lam alpha hlam ha z hsmall N
  · exact scaledOutputGram_positivePowers_traceNorm_error_le_kummer
      lam alpha hlam ha z hsmall N

/-- A common upper bound also controls simultaneously the
two *different* ambient bounded-operator truncation errors. -/
theorem dualGrams_simultaneous_operatorNorm_geometric_error_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    max
      (‖((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1 -
         ((∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1‖)
      (‖((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1 -
         ((∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1‖) ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  apply max_le
  · exact scaledGram_positivePowers_operatorNorm_error_le_kummer
      lam alpha hlam ha z hsmall N
  · exact scaledOutputGram_positivePowers_operatorNorm_error_le_kummer
      lam alpha hlam ha z hsmall N

#print axioms GegenbauerFock.GeneralUltrasphericalFock.scaled_dualGrams_traceNorm_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_simultaneous_traceNorm_geometric_error_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_simultaneous_operatorNorm_geometric_error_le

end GegenbauerFock.GeneralUltrasphericalFock
