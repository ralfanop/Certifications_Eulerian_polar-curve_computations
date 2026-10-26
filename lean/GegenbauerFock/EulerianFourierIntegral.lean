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

#print axioms GegenbauerFock.EulerianFourier.eulerian_fourier_at_one
#print axioms GegenbauerFock.EulerianFourier.eulerian_fourier_at_one_sin

end GegenbauerFock.EulerianFourier
