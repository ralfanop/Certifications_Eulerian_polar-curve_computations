import Mathlib
import SpecialImaginaryPoint.SonineEntireAveraging
import SpecialImaginaryPoint.SonineBesselCoefficients

/-!
# Manuscript 14.1 §4 — genuine Sonine integral maps J0 / I0 Taylor series to sinc

The theorems identify the *actual* Sonine Bochner interval integral with
the classical Complex.sin and Complex.sinh under the explicit
coefficient-series absolute-summability hypotheses. The hypotheses are
mathematically satisfied because the Bessel series are entire; a
separate Lean certificate of their universal summability will remove
them and make these results unconditional.
-/

namespace Manuscript14Sonine

noncomputable def modifiedBesselSeries (z : ℂ) : ℂ :=
  evenEntireSeries (fun n : ℕ => (modifiedBesselCoefficient n : ℂ)) z

noncomputable def ordinaryBesselSeries (z : ℂ) : ℂ :=
  evenEntireSeries (fun n : ℕ => (ordinaryBesselCoefficient n : ℂ)) z

private theorem complex_modified_coefficient (n : ℕ) :
    (moment n : ℂ) * (modifiedBesselCoefficient n : ℂ) =
      1 / (Nat.factorial (2*n+1) : ℂ) := by
  have h := congrArg (fun q : ℚ => (q : ℂ))
    (sonine_modifiedBessel_coefficients n)
  simpa [modifiedSphericalCoefficient] using h

private theorem complex_ordinary_coefficient (n : ℕ) :
    (moment n : ℂ) * (ordinaryBesselCoefficient n : ℂ) =
      (-1 : ℂ)^n / (Nat.factorial (2*n+1) : ℂ) := by
  have h := congrArg (fun q : ℚ => (q : ℂ))
    (sonine_ordinaryBessel_coefficients n)
  simpa [ordinarySphericalCoefficient, modifiedSphericalCoefficient, div_eq_mul_inv] using h

/-- For convergent I0 Taylor coefficients, the actual Sonine integral
    is a global modified-spherical profile at the chosen z. -/
theorem sonine_modifiedBessel_integral_mul (z : ℂ)
    (h : Summable (fun n : ℕ =>
      ‖(modifiedBesselCoefficient n : ℂ) * z^(2*n)‖)) :
    z * sonineAverageComplex modifiedBesselSeries z = Complex.sinh z := by
  change z * sonineAverageComplex
      (evenEntireSeries (fun n : ℕ => (modifiedBesselCoefficient n : ℂ))) z =
        Complex.sinh z
  rw [sonineAverageComplex_evenSeries _ z h]
  calc
    z * (∑' n : ℕ, (modifiedBesselCoefficient n : ℂ) *
        (moment n : ℂ) * z^(2*n)) =
      ∑' n : ℕ, z * ((modifiedBesselCoefficient n : ℂ) *
        (moment n : ℂ) * z^(2*n)) := by rw [tsum_mul_left]
    _ = ∑' n : ℕ, z^(2*n+1) / (Nat.factorial (2*n+1) : ℂ) := by
      congr 1
      funext n
      calc
        z * ((modifiedBesselCoefficient n : ℂ) *
            (moment n : ℂ) * z^(2*n)) =
          ((moment n : ℂ) * (modifiedBesselCoefficient n : ℂ)) *
            z^(2*n+1) := by rw [pow_succ]; ring
        _ = (1 / (Nat.factorial (2*n+1) : ℂ)) * z^(2*n+1) := by
          rw [complex_modified_coefficient]
        _ = z^(2*n+1) / (Nat.factorial (2*n+1) : ℂ) := by ring
    _ = Complex.sinh z := (Complex.hasSum_sinh z).tsum_eq

/-- Analogous statement for J0 and the classical complex sine. -/
theorem sonine_ordinaryBessel_integral_mul (z : ℂ)
    (h : Summable (fun n : ℕ =>
      ‖(ordinaryBesselCoefficient n : ℂ) * z^(2*n)‖)) :
    z * sonineAverageComplex ordinaryBesselSeries z = Complex.sin z := by
  change z * sonineAverageComplex
      (evenEntireSeries (fun n : ℕ => (ordinaryBesselCoefficient n : ℂ))) z =
        Complex.sin z
  rw [sonineAverageComplex_evenSeries _ z h]
  calc
    z * (∑' n : ℕ, (ordinaryBesselCoefficient n : ℂ) *
        (moment n : ℂ) * z^(2*n)) =
      ∑' n : ℕ, z * ((ordinaryBesselCoefficient n : ℂ) *
        (moment n : ℂ) * z^(2*n)) := by rw [tsum_mul_left]
    _ = ∑' n : ℕ, (-1 : ℂ)^n * z^(2*n+1) /
          (Nat.factorial (2*n+1) : ℂ) := by
      congr 1
      funext n
      calc
        z * ((ordinaryBesselCoefficient n : ℂ) *
            (moment n : ℂ) * z^(2*n)) =
          ((moment n : ℂ) * (ordinaryBesselCoefficient n : ℂ)) *
            z^(2*n+1) := by rw [pow_succ]; ring
        _ = ((-1 : ℂ)^n / (Nat.factorial (2*n+1) : ℂ)) *
            z^(2*n+1) := by rw [complex_ordinary_coefficient]
        _ = (-1 : ℂ)^n * z^(2*n+1) /
            (Nat.factorial (2*n+1) : ℂ) := by ring
    _ = Complex.sin z := (Complex.hasSum_sin z).tsum_eq

#print axioms Manuscript14Sonine.sonine_modifiedBessel_integral_mul
#print axioms Manuscript14Sonine.sonine_ordinaryBessel_integral_mul

end Manuscript14Sonine
