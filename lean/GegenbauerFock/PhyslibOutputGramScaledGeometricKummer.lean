import GegenbauerFock.PhyslibDualGramsActualS1NormEquality
import GegenbauerFock.PhyslibTraceClassGeometricTail

/-!
# V007 — scaled Fock-output Gram: geometric Kummer convergence rate

The full, nontruncated output Gram G_{λ,α} = C C* is a genuine
member of the complex Banach Schatten S₁ space. Its exact norm is the
unregularized Γ-normalized Kummer value
  ‖G_{λ,α}‖₁ = kummerSeries λ (1/(4α)).

For any complex coupling z satisfying
  ‖z‖ * kummerSeries λ (1/(4α)) < 1,
the nonunital geometric powers of z G_{λ,α} admit an explicit
finite-truncation error bound in true CFC trace norm AND operator norm.

This application does not treat the trace-class algebra as unital and
does not assume positivity of z or a finite-dimensional truncation.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The exact S₁ norm of the scaled, infinite ultraspherical Gram. -/
theorem scaledOutputGramTraceClass_actual_norm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) :
    ‖z • outputGramTraceClass lam alpha hlam ha‖ =
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [norm_smul, outputGramTraceClass_actual_norm_eq_kummer]

/-- Under the exact Kummer-based coupling criterion, the
nonunital Gram geometric powers converge at a certified rate
in the genuine CFC Schatten trace norm. -/
theorem scaledOutputGram_positivePowers_traceNorm_error_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    ProbabilisticTheory.TraceClass.traceNorm _
      ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) -
        (∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n)) ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  have hnorm := scaledOutputGramTraceClass_actual_norm_eq_kummer
    lam alpha hlam ha z
  have hc : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [hnorm]
    exact hsmall
  simpa only [hnorm] using
    (ProbabilisticTheory.TraceClass.positivePowers_traceNorm_error_le_geometric
      (z • outputGramTraceClass lam alpha hlam ha) hc N)

/-- The same explicit Gamma–Kummer numerical rate controls the
ambient operator-norm error of the scaled Fock-output Gram. -/
theorem scaledOutputGram_positivePowers_operatorNorm_error_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    ‖((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
        (z • outputGramTraceClass lam alpha hlam ha) n) :
          ProbabilisticTheory.TraceClass
            InfiniteAnalysis.FockCoefficients).1 -
      ((∑ n ∈ Finset.range N, ProbabilisticTheory.TraceClass.positivePower
        (z • outputGramTraceClass lam alpha hlam ha) n) :
          ProbabilisticTheory.TraceClass
            InfiniteAnalysis.FockCoefficients).1‖ ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  have hnorm := scaledOutputGramTraceClass_actual_norm_eq_kummer
    lam alpha hlam ha z
  have hc : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
    rw [hnorm]
    exact hsmall
  simpa only [hnorm] using
    (ProbabilisticTheory.TraceClass.positivePowers_operatorNorm_error_le_geometric
      (z • outputGramTraceClass lam alpha hlam ha) hc N)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.scaledOutputGramTraceClass_actual_norm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.scaledOutputGram_positivePowers_traceNorm_error_le_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.scaledOutputGram_positivePowers_operatorNorm_error_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
