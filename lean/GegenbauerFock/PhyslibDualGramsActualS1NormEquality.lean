import GegenbauerFock.PhyslibGramActualS1NormKummer
import GegenbauerFock.PhyslibOutputGramTrace

/-!
# V007 — equal actual S₁ norms for the two Gegenbauer–Fock Grams

The nontruncated source Gram C†C acts on weighted L², whereas
the output Gram CC† acts on the distinct Fock coefficient Hilbert
space. Both are genuine trace-class elements of their own normed
Banach spaces. Their *ordinary Lean norm* is the same Kummer mass.

This is an equality of trace norms in different Hilbert spaces,
not an identification of their underlying operators or a claim
of equivalence of the two Hilbert spaces.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine Fock-output Gram as an element of the independently
certified normed trace class on the target coefficient space. -/
noncomputable def outputGramTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass InfiniteAnalysis.FockCoefficients :=
  ProbabilisticTheory.TraceClass.ofOperator _
    (outputGram lam alpha hlam ha)
    (outputGram_isTraceClass lam alpha hlam ha)

/-- The ordinary S₁ norm of the Fock-output Gram is exactly Kummer. -/
theorem outputGramTraceClass_actual_norm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖outputGramTraceClass lam alpha hlam ha‖ =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    ‖outputGramTraceClass lam alpha hlam ha‖ =
        ProbabilisticTheory.TraceClass.traceNorm _
          (outputGramTraceClass lam alpha hlam ha) :=
      ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm _
    _ = ProbabilisticTheory.traceNorm (outputGram lam alpha hlam ha)
          (outputGram_isTraceClass lam alpha hlam ha) := rfl
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      outputGram_traceNorm_eq_kummer lam alpha hlam ha

/-- The actual norm in source weighted L² and Fock output spaces agrees. -/
theorem dualGrams_actual_S1_norm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖gramTraceClass lam alpha hlam ha‖ =
      ‖outputGramTraceClass lam alpha hlam ha‖ := by
  rw [gramTraceClass_actual_norm_eq_kummer,
    outputGramTraceClass_actual_norm_eq_kummer]

/-- Both actual Banach-space trace norms have the same Gamma-corrected
regularized confluent hypergeometric value. -/
theorem outputGramTraceClass_actual_norm_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((‖outputGramTraceClass lam alpha hlam ha‖ : ℝ) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  rw [← dualGrams_actual_S1_norm_eq lam alpha hlam ha]
  exact gramTraceClass_actual_norm_eq_mathlibRegularizedKummer
    lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramTraceClass_actual_norm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_actual_S1_norm_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGramTraceClass_actual_norm_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
