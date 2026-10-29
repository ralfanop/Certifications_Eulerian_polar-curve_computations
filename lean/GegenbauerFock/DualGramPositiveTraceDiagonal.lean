import GegenbauerFock.PositiveTraceDiagonalSpectralBridge
import GegenbauerFock.PhyslibOutputGramTrace

/-!
# V007 — both true Gegenbauer–Fock Grams: trace sums in every Hilbert basis

The weighted-ultraspherical source Gram C†C and the Fock-coefficient
output Gram CC† act on distinct Hilbert spaces. Both are genuine
positive trace-class operators. In every complete Hilbert basis in
each space, their positive diagonal is summable and has sum equal
to the SAME exact unregularized Kummer expression.

This is independent of Hilbert-basis selection. It does NOT yet
construct a complete eigenbasis nor identify a particular index
family with spectral multiplicities.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- In every complete Hilbert basis of the ultraspherical source L²,
the true positive Gram diagonal is summable. -/
theorem sourceGram_diagonal_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Type*}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun i : w =>
      (inner ℂ (b i) (gram lam alpha hlam ha (b i))).re) := by
  exact HilbertSchmidtBasis.positiveTrace_diagonal_summable
    (gram lam alpha hlam ha)
    (gram_isTraceClass lam alpha hlam ha)
    (gram_nonneg lam alpha hlam ha) b

/-- The genuine source Gram trace in ANY complete Hilbert basis
is the unregularized Kummer mass, including its exact normalization. -/
theorem sourceGram_diagonal_tsum_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Type*}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : w,
      (inner ℂ (b i) (gram lam alpha hlam ha (b i))).re) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    _ = ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
          (gram_isTraceClass lam alpha hlam ha) :=
        (HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
          (gram lam alpha hlam ha)
          (gram_isTraceClass lam alpha hlam ha)
          (gram_nonneg lam alpha hlam ha) b).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_traceNorm_eq_kummer lam alpha hlam ha

/-- The Fock-output Gram CC† is positive on its own Hilbert space. -/
theorem outputGram_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    0 ≤ outputGram lam alpha hlam ha := by
  change 0 ≤ (C lam alpha hlam ha).comp (C lam alpha hlam ha).adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    ((ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self
        (C lam alpha hlam ha).adjoint))

/-- In any Hilbert basis of the genuine output Fock coefficient
space, the nonnegative output Gram diagonal is summable. -/
theorem outputGram_diagonal_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Type*}
    (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients) :
    Summable (fun i : w =>
      (inner ℂ (b i) (outputGram lam alpha hlam ha (b i))).re) := by
  exact HilbertSchmidtBasis.positiveTrace_diagonal_summable
    (outputGram lam alpha hlam ha)
    (outputGram_isTraceClass lam alpha hlam ha)
    (outputGram_nonneg lam alpha hlam ha) b

/-- The output Gram positive trace is the SAME Kummer mass
for every complete output basis, independently of the source basis. -/
theorem outputGram_diagonal_tsum_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {w : Type*}
    (b : HilbertBasis w ℂ InfiniteAnalysis.FockCoefficients) :
    (∑' i : w,
      (inner ℂ (b i) (outputGram lam alpha hlam ha (b i))).re) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    _ = ProbabilisticTheory.traceNorm (outputGram lam alpha hlam ha)
          (outputGram_isTraceClass lam alpha hlam ha) :=
        (HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
          (outputGram lam alpha hlam ha)
          (outputGram_isTraceClass lam alpha hlam ha)
          (outputGram_nonneg lam alpha hlam ha) b).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      outputGram_traceNorm_eq_kummer lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_diagonal_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_diagonal_tsum_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonneg
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_diagonal_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_diagonal_tsum_eq_kummer

end GegenbauerFock.GeneralUltrasphericalFock
