/-
Manuscript 15 — actual Borel probability law for Unif[-1/2,1/2].

We instantiate Mathlib's conditional measure of Lebesgue volume,
prove the conditioning interval has measure exactly one, and obtain
a genuine IsProbabilityMeasure instance. This supplies a measure-level
model for subsequent characteristic-function and moment formalizations.

The analytic characteristic function and probability-law uniqueness
are separate downstream theorems, not hidden assumptions here.
-/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib

open Real MeasureTheory
noncomputable section
namespace Manuscript15

/-- The centred, unit-length Borel interval. -/
def unitCentredInterval : Set ℝ :=
  Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- Actual conditional Lebesgue measure, not a symbolic law placeholder. -/
def centredUniformLaw : Measure ℝ :=
  ProbabilityTheory.cond (volume : Measure ℝ) unitCentredInterval

/-- The supporting real interval has exact Lebesgue measure one. -/
theorem unitCentredInterval_volume :
    (volume : Measure ℝ) unitCentredInterval = 1 := by
  unfold unitCentredInterval
  rw [Real.volume_Icc]
  norm_num

/-- The constructed uniform law is a genuine Borel probability measure. -/
theorem centredUniformLaw_isProbability :
    IsProbabilityMeasure centredUniformLaw := by
  unfold centredUniformLaw
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [unitCentredInterval_volume]
    norm_num
  · rw [unitCentredInterval_volume]
    norm_num

/-- The identity random variable has Mathlib's uniform distribution on
    the exact centred interval with respect to this law. -/
theorem centredUniformLaw_isUniform :
    MeasureTheory.pdf.IsUniform (id : ℝ → ℝ)
      unitCentredInterval centredUniformLaw (volume : Measure ℝ) := by
  exact MeasureTheory.pdf.IsUniform.cond

/-- The law assigns total mass one to its support interval. -/
theorem centredUniformLaw_interval_mass :
    centredUniformLaw unitCentredInterval = 1 := by
  unfold centredUniformLaw
  exact ProbabilityTheory.cond_apply_self
    (by rw [unitCentredInterval_volume]; norm_num)
    (by rw [unitCentredInterval_volume]; norm_num)

#print axioms Manuscript15.unitCentredInterval_volume
#print axioms Manuscript15.centredUniformLaw_isProbability
#print axioms Manuscript15.centredUniformLaw_isUniform
#print axioms Manuscript15.centredUniformLaw_interval_mass

end Manuscript15
