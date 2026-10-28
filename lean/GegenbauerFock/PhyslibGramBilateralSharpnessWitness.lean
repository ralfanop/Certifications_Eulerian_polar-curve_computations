import GegenbauerFock.PhyslibGramTwoSidedTraceNormSharp

/-!
# V007 — mathematical sharpness of the exact CFC bilateral Kummer bound

The operator inequality with numerical coefficient one has been
independently kernel-certified. To justify *optimality*, this file
shows that the real Kummer mass is at least one, that A=B=identity
saturates the inequality, and that no uniform coefficient c<1
can replace it.

No new convergence assumptions, numerical approximations, or extra
axioms. The positivity argument uses the nonnegative series terms
and the first nonzero term (n=0).
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The Kummer mass has positive unit vacuum contribution. -/
theorem kummerSeries_ge_one (lam z : ℝ)
    (hlam : 0 < lam) (hz : 0 ≤ z) :
    (1 : ℝ) ≤ kummerSeries lam z := by
  have hs := kummerSeries_summable lam z hlam hz
  have hnonneg (n : ℕ) :
      0 ≤ ratio lam n * (z ^ n / (Nat.factorial n : ℝ)) :=
    mul_nonneg (ratio_nonneg lam hlam n) (by positivity)
  have hprefix :
      (∑ n ∈ Finset.range 1,
        ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) ≤
        kummerSeries lam z := by
    exact hs.sum_le_tsum (Finset.range 1) (fun i _ => hnonneg i)
  simpa [kummerSeries, ratio] using hprefix

theorem kummerSeries_pos (lam z : ℝ)
    (hlam : 0 < lam) (hz : 0 ≤ z) :
    0 < kummerSeries lam z :=
  lt_of_lt_of_le (by norm_num) (kummerSeries_ge_one lam z hlam hz)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_ge_one
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_pos

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Identity multipliers exactly saturate the bilateral trace bound,
using the same genuine CFC traceNorm under different S₁ witnesses. -/
theorem gram_identity_traceNorm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm
      ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) *
        gram lam alpha hlam ha * 1)
      (gram_twoSided_isTraceClass lam alpha hlam ha 1 1) =
    KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (Ultraspherical.measure lam))
  calc
    ProbabilisticTheory.traceNorm
        ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
            Lp ℂ 2 (Ultraspherical.measure lam)) *
          gram lam alpha hlam ha * 1)
        (gram_twoSided_isTraceClass lam alpha hlam ha 1 1) =
      ProbabilisticTheory.traceNorm
        (gram lam alpha hlam ha)
        (gram_isTraceClass lam alpha hlam ha) := by
      rw [ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gram_twoSided_isTraceClass lam alpha hlam ha 1 1) b,
        ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gram_isTraceClass lam alpha hlam ha) b]
      simp only [one_mul, mul_one]
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_traceNorm_eq_kummer lam alpha hlam ha

/-- No strictly smaller universal prefactor works in the sharp
bilateral Gegenbauer-Fock trace-norm inequality. -/
theorem gram_bilateral_coefficient_one_optimal
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℝ) (hc : c < 1) :
    ¬ ∀ (A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)),
        ProbabilisticTheory.traceNorm
            (A * gram lam alpha hlam ha * B)
            (gram_twoSided_isTraceClass lam alpha hlam ha A B) ≤
          c * (‖A‖ * ‖B‖ *
            KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  intro h
  have hI := h 1 1
  rw [gram_identity_traceNorm_eq_kummer lam alpha hlam ha] at hI
  simp only [norm_one, one_mul] at hI
  have harg : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hp : 0 < KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
    KummerCoefficients.kummerSeries_pos lam (1 / (4 * alpha)) hlam harg
  nlinarith

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_identity_traceNorm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_bilateral_coefficient_one_optimal

end GegenbauerFock.GeneralUltrasphericalFock
