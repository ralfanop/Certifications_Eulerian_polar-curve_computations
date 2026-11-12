import Manuscript15.EulerianCharacteristicIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Manuscript 15 — actual probability measure realizing the Eulerian sinc profile

The Eulerian Fourier profile rE(t)=sinc(t/2) from Manuscript 11
was independently shown in the preceding module to equal the
EXACT complex interval Fourier integral ∫_{-1/2}^{1/2} exp(i t x) dx.

We now construct the actual unit-mass Borel measure
  μ_E = Lebesgue_volume.restrict [-1/2,1/2]
and prove its total mass is exactly 1. The characteristic function
of this genuine probability measure is the same Eulerian profile rE
at EVERY real frequency, including the removable t=0.

These statements are classical harmonic/probability analysis.
This is a genuine measure-theoretic realization, not an assertion
that the formal coefficient recurrence alone has produced the measure.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Real Set intervalIntegral
open scoped Real

/-- Actual normalized Lebesgue probability measure of the
closed symmetric interval [-1/2,1/2] on the real line. -/
noncomputable def eulerianUniformMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict
    (Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ))

/-- The actual centered interval measure has total mass precisely one.
The interval has length (1/2)-(-1/2)=1, so no extra normalizer appears. -/
instance eulerianUniformMeasure_isProbabilityMeasure :
    IsProbabilityMeasure eulerianUniformMeasure where
  measure_univ := by
    simp [eulerianUniformMeasure, Real.volume_Icc]
    norm_num

/-- The genuine Borel probability measure on [-1/2,1/2] has
Eulerian sinc as its COMPLETE complex characteristic function.
This includes t=0 and does not rely on finite Taylor truncation. -/
theorem eulerianUniformMeasure_charFun (t : ℝ) :
    charFun eulerianUniformMeasure t =
      (EulerianCert.FourierModes.rE t : ℂ) := by
  have hIcc :
      (∫ x in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂volume) =
      (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
  calc
    charFun eulerianUniformMeasure t =
        ∫ x in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂volume := by
      simp [charFun_apply_real, eulerianUniformMeasure]
    _ = ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := hIcc
    _ = (EulerianCert.FourierModes.rE t : ℂ) :=
      eulerian_sinc_eq_symmetric_interval_fourierIntegral t

#print axioms Manuscript15.eulerianUniformMeasure_charFun

end Manuscript15
