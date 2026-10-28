import GegenbauerFock.UltrasphericalMeasure

/-!
# V007 — positive mass on every interior ultraspherical interval

This module establishes a missing measure-theoretic prerequisite for
analytic uniqueness: the actual Beta-pushforward ultraspherical law
assigns strictly positive mass to every nonempty open interval lying
inside (-1,1). This is stronger than merely showing positivity of the
candidate affine density, and uses the genuine measure.

It does not yet prove analytic uniqueness or unconditional density of
the Fock output range.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace GegenbauerFock.Ultraspherical

/-- Every nonempty open interval strictly inside the Beta support
has positive measure under the actual symmetric Beta probability law. -/
theorem betaMeasure_Ioo_pos
    (lam a b : ℝ) (hlam : 0 < lam)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < ProbabilityTheory.betaMeasure (shape lam) (shape lam) (Set.Ioo a b) := by
  rw [ProbabilityTheory.betaMeasure, MeasureTheory.withDensity_apply _ measurableSet_Ioo]
  apply (MeasureTheory.setLIntegral_pos_iff
    (show Measurable (ProbabilityTheory.betaPDF (shape lam) (shape lam)) by
      unfold ProbabilityTheory.betaPDF
      fun_prop)).2
  have hsubset :
      Set.Ioo a b ⊆
        Function.support (ProbabilityTheory.betaPDF (shape lam) (shape lam)) ∩
          Set.Ioo a b := by
    intro x hx
    refine ⟨?_, hx⟩
    change ProbabilityTheory.betaPDF (shape lam) (shape lam) x ≠ 0
    unfold ProbabilityTheory.betaPDF
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact ProbabilityTheory.betaPDFReal_pos
      (lt_of_le_of_lt ha hx.1) (lt_of_lt_of_le hx.2 hb)
      (shape_pos lam hlam) (shape_pos lam hlam)
  have hv : (0 : ℝ≥0∞) < volume (Set.Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact lt_of_lt_of_le hv (measure_mono hsubset)

/-- Every nonempty open interval in (-1,1) has positive mass under
the *actual transported* ultraspherical measure νλ. -/
theorem measure_Ioo_pos
    (lam a b : ℝ) (hlam : 0 < lam)
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < measure lam (Set.Ioo a b) := by
  have hleft : 0 ≤ (a + 1) / 2 := by linarith
  have hmiddle : (a + 1) / 2 < (b + 1) / 2 := by linarith
  have hright : (b + 1) / 2 ≤ 1 := by linarith
  have hpre :
      Set.Ioo ((a + 1) / 2) ((b + 1) / 2) ⊆
        betaToInterval ⁻¹' Set.Ioo a b := by
    intro x hx
    change a < 2 * x - 1 ∧ 2 * x - 1 < b
    constructor <;> linarith [hx.1, hx.2]
  have hmeas : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  unfold measure
  rw [Measure.map_apply hmeas measurableSet_Ioo]
  exact lt_of_lt_of_le
    (betaMeasure_Ioo_pos lam ((a + 1) / 2) ((b + 1) / 2)
      hlam hleft hmiddle hright)
    (measure_mono hpre)

#print axioms GegenbauerFock.Ultraspherical.betaMeasure_Ioo_pos
#print axioms GegenbauerFock.Ultraspherical.measure_Ioo_pos

end GegenbauerFock.Ultraspherical
