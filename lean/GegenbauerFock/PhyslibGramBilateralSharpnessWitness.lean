import GegenbauerFock.PhyslibGramTwoSidedTraceNormSharp
import GegenbauerFock.KummerPositiveBounds

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

/-- Strict positivity from the separately certified nonnegative Kummer series. -/
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
  let H := Lp ℂ 2 (Ultraspherical.measure lam)
  let K : ℝ := KummerCoefficients.kummerSeries lam (1 / (4 * alpha))
  have hI := h 1 1
  rw [gram_identity_traceNorm_eq_kummer lam alpha hlam ha] at hI
  change K ≤ c * (‖(1 : H →L[ℂ] H)‖ * ‖(1 : H →L[ℂ] H)‖ * K) at hI
  have harg : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hp : 0 < K :=
    KummerCoefficients.kummerSeries_pos lam (1 / (4 * alpha)) hlam harg
  have hnorm : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ H‖ ≤ (1 : ℝ)
    exact ContinuousLinearMap.norm_id_le
  have hnormsq : ‖(1 : H →L[ℂ] H)‖ ^ 2 ≤ (1 : ℝ) :=
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hnorm
  have hscale : ‖(1 : H →L[ℂ] H)‖ *
      ‖(1 : H →L[ℂ] H)‖ * K ≤ K := by
    have hsq : ‖(1 : H →L[ℂ] H)‖ *
        ‖(1 : H →L[ℂ] H)‖ ≤ (1 : ℝ) := by
      nlinarith [hnormsq]
    calc
      _ ≤ 1 * K := mul_le_mul_of_nonneg_right hsq hp.le
      _ = K := one_mul _
  have hfactor : 0 ≤ ‖(1 : H →L[ℂ] H)‖ *
      ‖(1 : H →L[ℂ] H)‖ * K := by positivity
  by_cases hc_nonpos : c ≤ 0
  · have hrhs : c * (‖(1 : H →L[ℂ] H)‖ *
        ‖(1 : H →L[ℂ] H)‖ * K) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc_nonpos hfactor
    linarith
  · have hcpos : 0 ≤ c := le_of_lt (lt_of_not_ge hc_nonpos)
    have hlim : K ≤ c * K := by
      calc
        K ≤ c * (‖(1 : H →L[ℂ] H)‖ *
            ‖(1 : H →L[ℂ] H)‖ * K) := hI
        _ ≤ c * K := mul_le_mul_of_nonneg_left hscale hcpos
    nlinarith [mul_pos (sub_pos.mpr hc) hp]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_identity_traceNorm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_bilateral_coefficient_one_optimal

end GegenbauerFock.GeneralUltrasphericalFock
