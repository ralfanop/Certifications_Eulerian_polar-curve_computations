import GegenbauerFock.PhyslibDualGramsSimultaneousGeometricKummer
import GegenbauerFock.PhyslibTraceClassNeumannGeometricBridge

/-!
# V007 — concrete Kummer-controlled Neumann corrections for BOTH Grams

The exact Gamma-Kummer trace mass provides one sufficient
convergence criterion q=‖z‖·KummerSeries(λ,1/(4α)) < 1 for
the full source Gram C* C and the output Gram C C*.

The actual positive-power sums (whose tails were certified
previously) satisfy the two-sided nonunital Neumann equations.
Their true S₁ trace norms both admit the same q/(1-q) majorant.

The corrections inhabit distinct trace-class Banach rings on
different Hilbert spaces: no source-output identification occurs.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The *same* source-Gram positive powers as in the Kummer geometric
tail theorem satisfy two-sided Neumann equations in the S₁ ideal. -/
theorem sourceGram_positivePowers_Kummer_neumann
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • gramTraceClass lam alpha hlam ha
    (T + (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) * T =
      ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) ∧
    (T + T * (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) =
      ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) := by
  dsimp
  apply ProbabilisticTheory.TraceClass.positivePowers_two_sided_Neumann
  rw [scaledGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

/-- The output-Gram positive powers obey identical nonunital
Neumann equations in their *different* Fock coefficient S₁ ideal. -/
theorem outputGram_positivePowers_Kummer_neumann
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    (T + (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) * T =
      ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) ∧
    (T + T * (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) =
      ∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower T n) := by
  dsimp
  apply ProbabilisticTheory.TraceClass.positivePowers_two_sided_Neumann
  rw [scaledOutputGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

/-- A uniform, explicit, Gamma–Kummer trace-norm bound holds
for the two genuinely different Neumann corrections at once. -/
theorem dualGrams_positivePowers_total_traceNorm_le_Kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    max
      (ProbabilisticTheory.TraceClass.traceNorm _
        (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • gramTraceClass lam alpha hlam ha) n))
      (ProbabilisticTheory.TraceClass.traceNorm _
        (∑' n : ℕ, ProbabilisticTheory.TraceClass.positivePower
          (z • outputGramTraceClass lam alpha hlam ha) n)) ≤
      (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) /
      (1 - ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  apply max_le
  · have hn := scaledGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
    have hc : ‖z • gramTraceClass lam alpha hlam ha‖ < 1 := by
      rw [hn]
      exact hsmall
    simpa only [hn] using
      (ProbabilisticTheory.TraceClass.positivePowers_total_traceNorm_le
        (z • gramTraceClass lam alpha hlam ha) hc)
  · have hn := scaledOutputGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
    have hc : ‖z • outputGramTraceClass lam alpha hlam ha‖ < 1 := by
      rw [hn]
      exact hsmall
    simpa only [hn] using
      (ProbabilisticTheory.TraceClass.positivePowers_total_traceNorm_le
        (z • outputGramTraceClass lam alpha hlam ha) hc)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_positivePowers_Kummer_neumann
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_positivePowers_Kummer_neumann
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_positivePowers_total_traceNorm_le_Kummer

end GegenbauerFock.GeneralUltrasphericalFock
