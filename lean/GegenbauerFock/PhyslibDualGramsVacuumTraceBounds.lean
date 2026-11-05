import GegenbauerFock.PhyslibDualGramsActualS1NormEquality
import GegenbauerFock.KummerPositiveBounds

/-!
# V007 — quantitative vacuum excess of both exact CFC Schatten S₁ Grams

The actual trace-class norms of the source Gram C†C and the target
Gram CC† have the same unregularized Kummer value K(λ,1/(4α)).
Its n=0 vacuum contribution is exactly 1, all terms are nonnegative,
and 0≤K-1≤exp(1/(4α))-1.

These quantitative estimates apply in the two *different* complex
Hilbert spaces, without identifying the operators or their source
and target spaces. They are fully uniform in λ>0 for each α>0.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The two exact trace norms are between their unit vacuum
contribution and the parameter-only exponential envelope. -/
theorem dualGrams_actual_S1_vacuum_exponential_bounds
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((1 : ℝ) ≤ ‖gramTraceClass lam alpha hlam ha‖ ∧
        ‖gramTraceClass lam alpha hlam ha‖ ≤ Real.exp (1 / (4 * alpha))) ∧
      ((1 : ℝ) ≤ ‖outputGramTraceClass lam alpha hlam ha‖ ∧
        ‖outputGramTraceClass lam alpha hlam ha‖ ≤ Real.exp (1 / (4 * alpha))) := by
  have hz : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hlo := KummerCoefficients.kummerSeries_ge_one
    lam (1 / (4 * alpha)) hlam hz
  have hhi := KummerCoefficients.kummerSeries_le_exp
    lam (1 / (4 * alpha)) hlam hz
  constructor
  · rw [gramTraceClass_actual_norm_eq_kummer]
    exact ⟨hlo, hhi⟩
  · rw [outputGramTraceClass_actual_norm_eq_kummer]
    exact ⟨hlo, hhi⟩

/-- The excess S₁ norm over the Fock vacuum mass is nonnegative
and at most exp(1/(4α))-1 for both nontruncated Grams. -/
theorem dualGrams_actual_S1_vacuum_excess_bounds
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 ≤ ‖gramTraceClass lam alpha hlam ha‖ - 1 ∧
      ‖gramTraceClass lam alpha hlam ha‖ - 1 ≤
        Real.exp (1 / (4 * alpha)) - 1) ∧
    (0 ≤ ‖outputGramTraceClass lam alpha hlam ha‖ - 1 ∧
      ‖outputGramTraceClass lam alpha hlam ha‖ - 1 ≤
        Real.exp (1 / (4 * alpha)) - 1) := by
  obtain ⟨⟨hsl, hsu⟩, ⟨hol, hou⟩⟩ :=
    dualGrams_actual_S1_vacuum_exponential_bounds lam alpha hlam ha
  exact ⟨⟨sub_nonneg.mpr hsl, sub_le_sub_right hsu 1⟩,
    ⟨sub_nonneg.mpr hol, sub_le_sub_right hou 1⟩⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_actual_S1_vacuum_exponential_bounds
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_actual_S1_vacuum_excess_bounds

end GegenbauerFock.GeneralUltrasphericalFock
