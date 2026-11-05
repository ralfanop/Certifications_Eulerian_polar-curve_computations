import Mathlib
import SpecialImaginaryPoint.SonineFactorialMoment

/-!
# Manuscript 14.1 §4 — exact Sonine action on J0 and I0 coefficients

For every natural n, the Sonine moment maps the order-zero
cylindrical Bessel J0 / modified-Bessel I0 Taylor coefficient to
the corresponding spherical sinc / hyperbolic sinc coefficient.
This is a universal exact rational coefficient identity, not yet
a theorem identifying the actual integrals of the globally
analytic Bessel functions (the latter needs infinite-sum
interchange, developed in SonineEntireInterchange.lean).
-/

namespace Manuscript14Sonine

/-- Coefficient of z^(2n) in I₀(z). -/
def modifiedBesselCoefficient (n : ℕ) : ℚ :=
  1 / ((4 : ℚ)^n * (Nat.factorial n : ℚ)^2)

/-- Coefficient of z^(2n) in sinh(z)/z. -/
def modifiedSphericalCoefficient (n : ℕ) : ℚ :=
  1 / (Nat.factorial (2*n+1) : ℚ)

/-- Exact rational map of all modified-Bessel coefficients. -/
theorem sonine_modifiedBessel_coefficients (n : ℕ) :
    moment n * modifiedBesselCoefficient n =
      modifiedSphericalCoefficient n := by
  rw [moment_eq_factorialMoment]
  unfold factorialMoment modifiedBesselCoefficient modifiedSphericalCoefficient
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hden : (Nat.factorial (2*n+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*n+1)
  have hpow : (4 : ℚ)^n ≠ 0 := by positivity
  field_simp [hfac, hden, hpow] <;> ring

def ordinaryBesselCoefficient (n : ℕ) : ℚ :=
  (-1 : ℚ)^n * modifiedBesselCoefficient n

def ordinarySphericalCoefficient (n : ℕ) : ℚ :=
  (-1 : ℚ)^n * modifiedSphericalCoefficient n

/-- Exact rational map of all ordinary-Bessel coefficients. -/
theorem sonine_ordinaryBessel_coefficients (n : ℕ) :
    moment n * ordinaryBesselCoefficient n =
      ordinarySphericalCoefficient n := by
  simp only [ordinaryBesselCoefficient, ordinarySphericalCoefficient]
  calc
    moment n * ((-1 : ℚ)^n * modifiedBesselCoefficient n) =
      (-1 : ℚ)^n * (moment n * modifiedBesselCoefficient n) := by ring
    _ = (-1 : ℚ)^n * modifiedSphericalCoefficient n := by
      rw [sonine_modifiedBessel_coefficients]

#print axioms Manuscript14Sonine.sonine_modifiedBessel_coefficients
#print axioms Manuscript14Sonine.sonine_ordinaryBessel_coefficients

end Manuscript14Sonine
