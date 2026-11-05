import GegenbauerFock.PhyslibTraceClassNormedSpace
import GegenbauerFock.PhyslibTraceClassSubtype

/-!
# V007 — the actual norm of the ultraspherical Gram in the normed CFC S₁ type

This module upgrades the already-certified explicit Kummer trace
formula from the proof-carrying operator traceNorm to the **ordinary
Norm.norm of the genuine complex normed Schatten-S₁ space**.

The operator is the full, nontruncated Gegenbauer/Fock Gram on its
weighted L² Hilbert space. There is no new analytic hypothesis and
no alternative definition of trace norm. Completeness is not used.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The ordinary real norm on the actual trace-class normed space
coincides exactly with the original ultraspherical Kummer series. -/
theorem gramTraceClass_actual_norm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖gramTraceClass lam alpha hlam ha‖ =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    ‖gramTraceClass lam alpha hlam ha‖ =
        ProbabilisticTheory.TraceClass.traceNorm _
          (gramTraceClass lam alpha hlam ha) :=
      ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm _
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gramTraceClass_traceNorm_eq_kummer lam alpha hlam ha

/-- Gamma-corrected regularized complex Kummer value of the
ordinary norm of the genuine Schatten-S₁ Gram element. -/
theorem gramTraceClass_actual_norm_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((‖gramTraceClass lam alpha hlam ha‖ : ℝ) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  calc
    ((‖gramTraceClass lam alpha hlam ha‖ : ℝ) : ℂ) =
        ((ProbabilisticTheory.TraceClass.traceNorm _
          (gramTraceClass lam alpha hlam ha)) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ))
        (ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm _)
    _ = Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
          KummerCoefficients.mathlibRegularizedKummer lam
            (((1 / (4 * alpha) : ℝ) : ℂ)) :=
      gramTraceClass_traceNorm_eq_mathlibRegularizedKummer lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_actual_norm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_actual_norm_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
