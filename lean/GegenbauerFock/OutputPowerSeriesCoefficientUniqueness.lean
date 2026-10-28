import Mathlib
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# V007 — uniqueness of coefficients of a summable complex power series

This standalone lemma is the scalar-analytic step required for the
Gegenbauer--Fock output adjoint. Absolute summability of the coefficients
at z = 1 gives positive convergence radius; if the resulting complex
power series vanishes identically, uniqueness of one-dimensional
formal multilinear series makes every coefficient vanish.

No operator injectivity is assumed. The application to the actual
Fock coefficients will supply the summability hypothesis from the
certified coherent-vector Cauchy--Schwarz estimate.
-/

noncomputable section

open FormalMultilinearSeries
open scoped ENNReal

namespace GegenbauerFock.FockEvaluation

/-- Absolute summability at z=1 and global vanishing of a complex
power series imply that ALL coefficients vanish. In contrast to
mere differentiation of a finite truncation, the proof uses the
uniqueness theorem for a convergent infinite formal multilinear series. -/
theorem complex_coefficients_zero_of_tsum_monomial_zero
    (c : ℕ → ℂ)
    (hs : Summable (fun n : ℕ => ‖c n‖))
    (hz : ∀ z : ℂ, (∑' n : ℕ, c n * z ^ n) = 0) :
    ∀ n : ℕ, c n = 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ c
  have hs' : Summable
      (fun n : ℕ => ‖p n‖ * (((1 : ℝ≥0) : ℝ) ^ n)) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_norm,
      NNReal.coe_one, one_pow, mul_one] using hs
  have hr_le : (1 : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_summable (r := (1 : ℝ≥0)) hs'
  have hr_pos : (0 : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hr_le
  have hsum (z : ℂ) :
      p.sum z = ∑' n : ℕ, c n * z ^ n := by
    simpa only [p, FormalMultilinearSeries.ofScalarsSum,
      smul_eq_mul] using
      (FormalMultilinearSeries.ofScalars_sum_eq (E := ℂ) c z)
  have hfun : p.sum = (0 : ℂ → ℂ) := by
    funext z
    exact (hsum z).trans (hz z)
  have hp : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    have h := (p.hasFPowerSeriesOnBall hr_pos).hasFPowerSeriesAt
    rw [hfun] at h
    exact h
  have hc : c = 0 :=
    (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ)).mp
      (show FormalMultilinearSeries.ofScalars ℂ c = 0 from hp.eq_zero)
  intro n
  exact congrArg (fun d : ℕ → ℂ => d n) hc

#print axioms GegenbauerFock.FockEvaluation.complex_coefficients_zero_of_tsum_monomial_zero

end GegenbauerFock.FockEvaluation
