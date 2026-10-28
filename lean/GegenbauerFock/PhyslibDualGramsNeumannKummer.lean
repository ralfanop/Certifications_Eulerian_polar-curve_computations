import GegenbauerFock.PhyslibDualGramsSimultaneousGeometricKummer
import GegenbauerFock.PhyslibTraceClassNeumannQuasiregular

/-!
# V007 — exact Kummer radius for two-sided nonunital Gram resolvent corrections

The operator C* C is trace-class on the ultraspherical weighted L² Hilbert
space, while C C* acts on a *different* Fock coefficient Hilbert space.
Their actual S₁ norms coincide with the same Gamma-Kummer value.

For any λ,α>0 and complex z satisfying
    ‖z‖ · KummerSeries(λ, 1/(4α)) < 1,
Mathlib's genuine nonunital Banach-ring Neumann theorem yields both
two-sided quasiregular identities, *separately*, for the scaled Grams.
There is no claim that the two Grams are the same operator, and no
unit operator is inserted into the trace-class ideal.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The negative of the exact scaled source Gram is quasiregular in
the genuine CFC Schatten S₁ Banach ring on weighted L². -/
theorem sourceGram_Kummer_negative_quasiregular
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsQuasiregular (-(z • gramTraceClass lam alpha hlam ha)) := by
  apply ProbabilisticTheory.TraceClass.neumann_negative_quasiregular
  rw [scaledGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

/-- The negative of the exact scaled output Gram is quasiregular in
the genuine CFC Schatten S₁ Banach ring on Fock coefficients. -/
theorem outputGram_Kummer_negative_quasiregular
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsQuasiregular (-(z • outputGramTraceClass lam alpha hlam ha)) := by
  apply ProbabilisticTheory.TraceClass.neumann_negative_quasiregular
  rw [scaledOutputGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

/-- The single explicit Gamma-Kummer coupling criterion certifies
quasiregularity in both distinct Hilbert spaces simultaneously. -/
theorem dualGrams_Kummer_negative_quasiregular
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    IsQuasiregular (-(z • gramTraceClass lam alpha hlam ha)) ∧
    IsQuasiregular (-(z • outputGramTraceClass lam alpha hlam ha)) :=
  ⟨sourceGram_Kummer_negative_quasiregular lam alpha hlam ha z hsmall,
   outputGram_Kummer_negative_quasiregular lam alpha hlam ha z hsmall⟩

/-- Exact two-sided Neumann identities for the nonunital source Gram
correction S=∑_(n≥0) (· * zC*C)^[n] (zC*C). -/
theorem sourceGram_Kummer_neumann_two_sided
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • gramTraceClass lam alpha hlam ha
    (T + (∑' n : ℕ, (· * T)^[n] T) * T =
      ∑' n : ℕ, (· * T)^[n] T) ∧
    (T + T * (∑' n : ℕ, (· * T)^[n] T) =
      ∑' n : ℕ, (· * T)^[n] T) := by
  dsimp
  apply ProbabilisticTheory.TraceClass.neumann_two_sided_identities
  rw [scaledGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

/-- Exact two-sided Neumann identities in the distinct coefficient-Fock
Hilbert space for the nonunital output Gram CC*. -/
theorem outputGram_Kummer_neumann_two_sided
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ)
    (hsmall :
      ‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) < 1) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    (T + (∑' n : ℕ, (· * T)^[n] T) * T =
      ∑' n : ℕ, (· * T)^[n] T) ∧
    (T + T * (∑' n : ℕ, (· * T)^[n] T) =
      ∑' n : ℕ, (· * T)^[n] T) := by
  dsimp
  apply ProbabilisticTheory.TraceClass.neumann_two_sided_identities
  rw [scaledOutputGramTraceClass_actual_norm_eq_kummer]
  exact hsmall

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_Kummer_negative_quasiregular
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_Kummer_negative_quasiregular
#print axioms GegenbauerFock.GeneralUltrasphericalFock.dualGrams_Kummer_negative_quasiregular
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_Kummer_neumann_two_sided
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_Kummer_neumann_two_sided

end GegenbauerFock.GeneralUltrasphericalFock
