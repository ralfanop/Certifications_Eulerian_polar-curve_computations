import GegenbauerFock.PhyslibDualGramsExplicitKummerResolvent
import GegenbauerFock.PhyslibDualGramsSimultaneousGeometricKummer

/-!
# V007 — certified finite approximate ambient Gram resolvents

The exact inverse of (1 - z G) in the ambient bounded-operator algebra
is I + S, where S is the trace-class nonunital sum of positive powers.

The *finite* resolvent approximation is I plus the first N
positive powers. The norm error is bounded by
  q^(N+1)/(1-q), q=‖z‖·KummerSeries λ (1/(4α))<1,
on each of two different weighted-L² and coefficient-Fock spaces.

Unlike a bare trace-class series tail, the statements below explicitly
retain the identity in the unital ambient operator algebra and certify
the error of the corresponding finite resolvent formula.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Genuine ambient bounded-operator error of the N-th finite
resolvent approximation on the ultraspherical source Hilbert space. -/
theorem sourceGram_finite_Kummer_resolvent_error_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    let T := z • gramTraceClass lam alpha hlam ha
    ‖((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) +
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) :
          ProbabilisticTheory.TraceClass
            (Lp ℂ 2 (Ultraspherical.measure lam))).1) -
      (1 + ((∑ n ∈ Finset.range N,
            ProbabilisticTheory.TraceClass.positivePower T n) :
          ProbabilisticTheory.TraceClass
            (Lp ℂ 2 (Ultraspherical.measure lam))).1)‖ ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  dsimp
  have hcancel :
      ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) +
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1) -
      (1 + ((∑ n ∈ Finset.range N,
        ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1) =
      ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1 -
      ((∑ n ∈ Finset.range N,
        ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              (Lp ℂ 2 (Ultraspherical.measure lam))).1 := by
    abel
  rw [hcancel]
  exact scaledGram_positivePowers_operatorNorm_error_le_kummer
    lam alpha hlam ha z hsmall N

/-- Genuine ambient bounded-operator error of the N-th finite
resolvent approximation on the coefficient-Fock target Hilbert space. -/
theorem outputGram_finite_Kummer_resolvent_error_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1)
    (N : ℕ) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    ‖((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) +
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) :
          ProbabilisticTheory.TraceClass
            InfiniteAnalysis.FockCoefficients).1) -
      (1 + ((∑ n ∈ Finset.range N,
            ProbabilisticTheory.TraceClass.positivePower T n) :
          ProbabilisticTheory.TraceClass
            InfiniteAnalysis.FockCoefficients).1)‖ ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam
        (1 / (4 * alpha))) ^ (N + 1) /
        (1 - ‖z‖ * KummerCoefficients.kummerSeries lam
          (1 / (4 * alpha))) := by
  dsimp
  have hcancel :
      ((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients) +
        ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1) -
      (1 + ((∑ n ∈ Finset.range N,
        ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1) =
      ((∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1 -
      ((∑ n ∈ Finset.range N,
        ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n) :
            ProbabilisticTheory.TraceClass
              InfiniteAnalysis.FockCoefficients).1 := by
    abel
  rw [hcancel]
  exact scaledOutputGram_positivePowers_operatorNorm_error_le_kummer
    lam alpha hlam ha z hsmall N

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_finite_Kummer_resolvent_error_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_finite_Kummer_resolvent_error_le

end GegenbauerFock.GeneralUltrasphericalFock
