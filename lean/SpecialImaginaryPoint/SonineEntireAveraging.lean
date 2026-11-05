import Mathlib
import SpecialImaginaryPoint.SonineEntireInterchange

/-!
# Manuscript 14.1 §4 — actual Sonine integral of an entire even Taylor series

For a coefficient sequence whose even series is absolutely convergent at
a specified complex parameter z, the actual Sonine integral equals the
transformed coefficient series. Under convergence for ALL z, this
identity is global on ℂ.

The proof uses the actual complex Bochner interval integral, the
dominated-convergence exchange theorem, and the certified monomial
moments. This does not yet prove the radial second-derivative
intertwining for all entire f; that is a further analytic step.
-/

namespace Manuscript14Sonine

open MeasureTheory intervalIntegral

noncomputable def evenEntireSeries (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z^(2*n)

/-- Actual Sonine average of an absolutely convergent complex even series. -/
theorem sonineAverageComplex_evenSeries (a : ℕ → ℂ) (z : ℂ)
    (h : Summable (fun n : ℕ => ‖a n * z^(2*n)‖)) :
    sonineAverageComplex (evenEntireSeries a) z =
      ∑' n : ℕ, a n * (moment n : ℂ) * z^(2*n) := by
  have hsum :
      HasSum (fun n : ℕ =>
        (1/2 : ℂ) * (∫ u in (-1 : ℝ)..1,
          a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)))
        (sonineAverageComplex (evenEntireSeries a) z) := by
    simpa only [sonineAverageComplex, evenEntireSeries] using
      (sonine_interval_hasSum a z h).mul_left (1/2 : ℂ)
  have hterm (n : ℕ) :
      (1/2 : ℂ) * (∫ u in (-1 : ℝ)..1,
          a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)) =
        a n * (moment n : ℂ) * z^(2*n) := by
    rw [intervalIntegral.integral_const_mul]
    have hmono := sonineAverageComplex_even_monomial n z
    unfold sonineAverageComplex at hmono
    calc
      (1/2 : ℂ) * (a n * (∫ u in (-1 : ℝ)..1,
          (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))) =
        a n * ((1/2 : ℂ) * (∫ u in (-1 : ℝ)..1,
          (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))) := by ring
      _ = a n * ((moment n : ℂ) * z^(2*n)) := by rw [hmono]
      _ = a n * (moment n : ℂ) * z^(2*n) := by ring
  have heq :
      (fun n : ℕ =>
        (1/2 : ℂ) * (∫ u in (-1 : ℝ)..1,
          a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))) =
      (fun n : ℕ => a n * (moment n : ℂ) * z^(2*n)) := by
    funext n
    exact hterm n
  rw [heq] at hsum
  exact hsum.tsum_eq.symm

/-- The global form, once the entire-series coefficient hypothesis is supplied. -/
theorem sonineAverageComplex_entireSeries (a : ℕ → ℂ)
    (h : ∀ z : ℂ, Summable (fun n : ℕ => ‖a n * z^(2*n)‖)) (z : ℂ) :
    sonineAverageComplex (evenEntireSeries a) z =
      ∑' n : ℕ, a n * (moment n : ℂ) * z^(2*n) :=
  sonineAverageComplex_evenSeries a z (h z)

#print axioms Manuscript14Sonine.sonineAverageComplex_evenSeries
#print axioms Manuscript14Sonine.sonineAverageComplex_entireSeries

end Manuscript14Sonine
