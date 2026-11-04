import Mathlib
import SpecialImaginaryPoint.SonineEntireAveraging
import SpecialImaginaryPoint.SonineRadialComplex

/-!
# Manuscript 14.1 §4 — analytic radial intertwining at the series-function level

The existing Lean theorem gives H₃ M = M H₂ on ALL complex formal even
coefficient sequences, and the new analytic theorem identifies the
genuine Sonine integral with coefficientwise M for absolutely
convergent even Taylor series.

This module combines those results to give an equality of COMPLEX
FUNCTION VALUES involving the actual Sonine interval integral and the
radial *series-coefficient* operators.

The remaining issue before identifying these coefficient operators
with classical second derivatives is the kernel formalization of
termwise differentiation of the entire series, including z=0.
-/

namespace Manuscript14Sonine

/-- Analytic representation of the two-dimensional radial generator,
    formed using its exact even Taylor coefficients. -/
noncomputable def evenRadial2Series (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  evenEntireSeries (radial2CoeffComplex a) z

/-- Analytic representation of the three-dimensional radial generator. -/
noncomputable def evenRadial3Series (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  evenEntireSeries (radial3CoeffComplex a) z

/-- Genuine integral intertwining on convergent complex even-series
    functions, expressed in radial Taylor coefficients. -/
theorem sonine_entire_radial_series_intertwining (a : ℕ → ℂ)
    (hRadial2 : ∀ z : ℂ,
      Summable (fun n : ℕ =>
        ‖radial2CoeffComplex a n * z^(2*n)‖)) (z : ℂ) :
    sonineAverageComplex (evenRadial2Series a) z =
      evenRadial3Series (sonineCoeffComplex a) z := by
  have hc (n : ℕ) :
      radial2CoeffComplex a n * (moment n : ℂ) =
        radial3CoeffComplex (sonineCoeffComplex a) n := by
    have h := congrFun (radial_intertwining_coeff_complex a) n
    dsimp [sonineCoeffComplex, momentComplex] at h
    rw [h]
    ring
  unfold evenRadial2Series evenRadial3Series
  calc
    sonineAverageComplex (evenEntireSeries (radial2CoeffComplex a)) z =
      ∑' n : ℕ,
        radial2CoeffComplex a n * (moment n : ℂ) * z^(2*n) :=
          sonineAverageComplex_evenSeries (radial2CoeffComplex a) z (hRadial2 z)
    _ = evenEntireSeries (radial3CoeffComplex (sonineCoeffComplex a)) z := by
      unfold evenEntireSeries
      congr 1
      funext n
      rw [hc n]

#print axioms Manuscript14Sonine.sonine_entire_radial_series_intertwining

end Manuscript14Sonine
