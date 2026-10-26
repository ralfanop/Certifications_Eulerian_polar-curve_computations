import Mathlib

/-!
# Eulerian profile: certified Fourier interval integral

This module specialises Mathlib's (proved) complex exponential Fourier
interval identity at r=1/2. This supplies an *actual interval-integral
identity* for the Eulerian profile at spatial frequency one, not merely
the algebraic kernel symbol.

It does not yet construct the full entire Paley–Wiener transform,
nor identify a Hilbert-space Fock operator.
-/

open intervalIntegral

namespace GegenbauerFock.EulerianFourier

/-- The interval Fourier average of a uniform law is the normalized sinc. -/
theorem eulerian_fourier_at_one :
    (∫ t : ℝ in (-(1/2:ℝ))..(1/2:ℝ),
        Complex.exp ((t:ℂ) * Complex.I)) =
      (Real.sinc (1/2:ℝ) : ℂ) := by
  simpa using (integral_exp_mul_I_eq_sinc (1/2:ℝ))

/-- A fully evaluated integral version in terms of the sine function. -/
theorem eulerian_fourier_at_one_sin :
    (∫ t : ℝ in (-(1/2:ℝ))..(1/2:ℝ),
        Complex.exp ((t:ℂ) * Complex.I)) =
      ((2 * Real.sin (1/2:ℝ)) : ℂ) := by
  simpa using (integral_exp_mul_I_eq_sin (1/2:ℝ))

/--
For any nonzero complex exponent, the uniform interval exponential
transform admits its exact endpoint quotient. This is the
frequency-dependent analytic precursor to the entire Eulerian profile.
-/
theorem interval_complex_exponential (w : ℂ) (hw : w ≠ 0) :
    (∫ t : ℝ in (-1/2:ℝ)..(1/2:ℝ),
        Complex.exp (w * (t:ℂ))) =
      (Complex.exp (w/2) - Complex.exp (-(w/2))) / w := by
  have h := integral_exp_mul_complex
    (a := (-1/2:ℝ)) (b := (1/2:ℝ)) (c := w) hw
  have hp : w * ((1/2:ℝ) : ℂ) = w / 2 := by norm_num <;> ring
  have hn : w * ((-1/2:ℝ) : ℂ) = -(w / 2) := by norm_num <;> ring
  simpa only [hp, hn] using h

/--
General nonzero complex Fourier-frequency formula.
The case z=0 is a separate removable-singularity statement.
-/
theorem eulerian_frequency_nonzero (z : ℂ) (hz : z ≠ 0) :
    (∫ t : ℝ in (-1/2:ℝ)..(1/2:ℝ),
        Complex.exp ((Complex.I*z) * (t:ℂ))) =
      (Complex.exp ((Complex.I*z)/2) -
        Complex.exp (-((Complex.I*z)/2))) / (Complex.I*z) := by
  exact interval_complex_exponential (Complex.I*z)
    (mul_ne_zero Complex.I_ne_zero hz)

#print axioms GegenbauerFock.EulerianFourier.interval_complex_exponential
#print axioms GegenbauerFock.EulerianFourier.eulerian_frequency_nonzero
#print axioms GegenbauerFock.EulerianFourier.eulerian_fourier_at_one
#print axioms GegenbauerFock.EulerianFourier.eulerian_fourier_at_one_sin

end GegenbauerFock.EulerianFourier
