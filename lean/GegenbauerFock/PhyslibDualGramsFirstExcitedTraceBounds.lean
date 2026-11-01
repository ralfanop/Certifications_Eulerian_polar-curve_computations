import GegenbauerFock.PhyslibDualGramsVacuumTraceBounds
import GegenbauerFock.KummerVacuumFirstCorrection

/-!
# V007 — strict nonvacuum trace mass in both genuine CFC Grams

The first positive Kummer term gives a nontrivial strict lower bound
on *both* actual trace-class norms of the weighted L² source Gram
C†C and the infinite Fock coefficient-output Gram CC†.
The two operators act on distinct Hilbert spaces: equality of their
S₁ norms does not identify their domains.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The first nonvacuum term is an exact simultaneous lower bound
for both positive trace-class Grams. -/
theorem dualGrams_actual_S1_first_vacuum_correction_lower
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (1 + KummerCoefficients.ratio lam 1 * (1 / (4 * alpha)) ≤
        ‖gramTraceClass lam alpha hlam ha‖) ∧
      (1 + KummerCoefficients.ratio lam 1 * (1 / (4 * alpha)) ≤
        ‖outputGramTraceClass lam alpha hlam ha‖) := by
  have hz : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  have hfirst := KummerCoefficients.kummerSeries_ge_vacuum_add_first
    lam (1 / (4 * alpha)) hlam hz
  constructor
  · rw [gramTraceClass_actual_norm_eq_kummer]
    exact hfirst
  · rw [outputGramTraceClass_actual_norm_eq_kummer]
    exact hfirst

/-- For all strictly positive parameters both nontruncated true S₁
Gram norms are strictly greater than their unit vacuum mass. -/
theorem dualGrams_actual_S1_strictly_above_vacuum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (1 : ℝ) < ‖gramTraceClass lam alpha hlam ha‖ ∧
      (1 : ℝ) < ‖outputGramTraceClass lam alpha hlam ha‖ := by
  have hz : 0 < (1 / (4 * alpha) : ℝ) := by positivity
  have hk := KummerCoefficients.kummerSeries_gt_one
    lam (1 / (4 * alpha)) hlam hz
  constructor
  · rw [gramTraceClass_actual_norm_eq_kummer]
    exact hk
  · rw [outputGramTraceClass_actual_norm_eq_kummer]
    exact hk

#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_actual_S1_first_vacuum_correction_lower
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_actual_S1_strictly_above_vacuum

end GegenbauerFock.GeneralUltrasphericalFock
