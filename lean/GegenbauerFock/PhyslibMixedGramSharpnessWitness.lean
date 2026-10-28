import GegenbauerFock.PhyslibGramBilateralSharpnessWitness
import GegenbauerFock.PhyslibMixedGramTraceNormSharp

/-!
# V007 — sharpness witness for the nonpositive mixed Gram trace norm

An off-diagonal mixed Gram B†GD is generally not positive. Its
genuine CFC-S1 estimate with the numerical coefficient 1 has been
certified separately. Here we prove the exact saturation B=D=1 and
show no real coefficient c<1 works simultaneously for every B,D.

The proof carefully transports the trace norm through a common
Hilbert basis; dependent S1-membership proof arguments are NOT
rewritten under a nondependent rewrite tactic.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

theorem gramMixed_identity_traceNorm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm
      (gramMixed lam alpha hlam ha
        (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) 1)
      (gramMixed_isTraceClass lam alpha hlam ha 1 1) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  let H := Lp ℂ 2 (Ultraspherical.measure lam)
  have heq : gramMixed lam alpha hlam ha
        (1 : H →L[ℂ] H) 1 = gram lam alpha hlam ha := by
    change (1 : H →L[ℂ] H).adjoint.comp
      ((gram lam alpha hlam ha).comp 1) =
        gram lam alpha hlam ha
    simp
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  calc
    ProbabilisticTheory.traceNorm
      (gramMixed lam alpha hlam ha
        (1 : H →L[ℂ] H) 1)
      (gramMixed_isTraceClass lam alpha hlam ha 1 1) =
      ProbabilisticTheory.traceNorm
        (gram lam alpha hlam ha)
        (gram_isTraceClass lam alpha hlam ha) := by
      rw [ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gramMixed_isTraceClass lam alpha hlam ha 1 1) b,
        ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
          (gram_isTraceClass lam alpha hlam ha) b, heq]
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_traceNorm_eq_kummer lam alpha hlam ha

/-- The coefficient 1 cannot be replaced uniformly by c<1 for
all bounded B,D, even though individual mixed Grams are nonpositive. -/
theorem gramMixed_coefficient_one_optimal
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℝ) (hc : c < 1) :
    ¬ ∀ (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)),
      ProbabilisticTheory.traceNorm
          (gramMixed lam alpha hlam ha B D)
          (gramMixed_isTraceClass lam alpha hlam ha B D) ≤
        c * (‖B‖ * ‖D‖ *
          KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  intro hb
  have hI := hb 1 1
  rw [gramMixed_identity_traceNorm_eq_kummer lam alpha hlam ha] at hI
  simp only [norm_one, one_mul] at hI
  have hz : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hp : 0 < KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
    KummerCoefficients.kummerSeries_pos lam (1 / (4 * alpha)) hlam hz
  nlinarith

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_identity_traceNorm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_coefficient_one_optimal

end GegenbauerFock.GeneralUltrasphericalFock
