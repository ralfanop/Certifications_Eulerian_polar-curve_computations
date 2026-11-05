import GegenbauerFock.PhyslibGramTwoSidedTraceNormSharp

/-!
# V007 — sharp nonpositive mixed Gegenbauer Gram trace norm

The certified concrete mixed S1 operator B†GD has, as a proposed
independent numerical bound, the exact optimal product of the
bounded multiplier norms and the previously certified Kummer trace.

The proof transports the CFC-absolute trace norm through the
operator identity by a common Hilbert basis; then it applies the
general sharp bilateral bound to A=B†. The adjoint is isometric.
This module is a candidate until independent Lean CI succeeds.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

theorem gramMixed_traceNorm_le_kummer_sharp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
        (gramMixed lam alpha hlam ha B D)
        (gramMixed_isTraceClass lam alpha hlam ha B D) ≤
      ‖B‖ * ‖D‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  have hmixed :
      gramMixed lam alpha hlam ha B D =
        B.adjoint * gram lam alpha hlam ha * D := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (Ultraspherical.measure lam))
  calc
    ProbabilisticTheory.traceNorm
        (gramMixed lam alpha hlam ha B D)
        (gramMixed_isTraceClass lam alpha hlam ha B D) =
      ProbabilisticTheory.traceNorm
        (B.adjoint * gram lam alpha hlam ha * D)
        (gram_twoSided_isTraceClass lam alpha hlam ha B.adjoint D) := by
      rw [ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gramMixed_isTraceClass lam alpha hlam ha B D) b,
        ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gram_twoSided_isTraceClass lam alpha hlam ha B.adjoint D) b,
        hmixed]
    _ ≤ ‖B.adjoint‖ * ‖D‖ *
          KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_twoSided_traceNorm_le_kummer_sharp
        lam alpha hlam ha B.adjoint D
    _ = ‖B‖ * ‖D‖ *
          KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_traceNorm_le_kummer_sharp

end GegenbauerFock.GeneralUltrasphericalFock
