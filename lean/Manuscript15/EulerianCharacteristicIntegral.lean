import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Manuscript 15 — exact Fourier integral of the Eulerian sinc profile

The Eulerian Fourier radius from the already certified Manuscript 11,
  rE(t) = sinc(t/2),
equals the COMPLEX Fourier integral of a unit-density measure on the
real symmetric interval [-1/2, 1/2]:

  ∫_{-1/2}^{1/2} exp(i t x) dx = (rE(t) : ℂ).

The proof uses Mathlib's exact integral of exp(i x) over [-r,r],
the exact interval-integral linear change of variable, and the
existing globally defined continuous sinc at the removable zero.

This establishes an essential analytic identity for the probability-
measure characteristic-function bridge; the identification of the
integral with the ProbabilityMeasure.charFun of a normalized restricted
Lebesgue measure is a SEPARATE formalization obligation.

The integral identity is classical Fourier analysis, not a newly
claimed theorem. No numerical approximations, conditional recurrence,
or probability-measure uniqueness hypothesis enter the proof.
-/

noncomputable section

namespace Manuscript15

open Real intervalIntegral
open scoped Real

/-- Actual complex Fourier integral of uniform unit density on
[-1/2, 1/2] equals the exact Eulerian sinc profile for EVERY real
frequency, including its removable origin. -/
theorem eulerian_sinc_eq_symmetric_interval_fourierIntegral
    (t : ℝ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
        (EulerianCert.FourierModes.rE t : ℂ) := by
  by_cases ht : t = 0
  · subst t
    norm_num [EulerianCert.FourierModes.rE_zero,
      intervalIntegral.integral_const]
  · have hchange :
        (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
            (t⁻¹ : ℝ) •
              (∫ y in -(t / 2)..(t / 2),
                Complex.exp ((y : ℂ) * Complex.I)) := by
      simpa only [show t * (-1 / 2 : ℝ) = -(t / 2) by ring,
        show t * (1 / 2 : ℝ) = t / 2 by ring] using
          (intervalIntegral.integral_comp_mul_left
            (f := fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
            (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) ht)
    rw [hchange, integral_exp_mul_I_eq_sin,
      EulerianCert.FourierModes.rE_of_ne_zero ht]
    change (t⁻¹ : ℝ) • ((2 : ℂ) * ↑(Real.sin (t / 2))) =
      ((2 * Real.sin (t / 2) / t : ℝ) : ℂ)
    rw [Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    field_simp [ht]
    ring

#print axioms Manuscript15.eulerian_sinc_eq_symmetric_interval_fourierIntegral

end Manuscript15
