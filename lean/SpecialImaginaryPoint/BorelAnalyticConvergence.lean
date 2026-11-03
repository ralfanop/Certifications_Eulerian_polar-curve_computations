import Mathlib

/-!
# Absolute convergence of the special-point double-Borel series

Manuscript 14, Theorems 3.3 and 3.5: this supplies the previously
missing convergence statement for the Eulerian double-Borel output
F(t) = ∑ n, (4^n / (2n+1)!) t^n.

The argument is absolute convergence at every complex parameter, using
a comparison with the entire exponential series.  This theorem does
not yet certify the analytic differential equation or termwise
differentiation, which remain separate obligations.
-/

namespace EulerianSpecialPoint

/-- The numerical coefficient of the entire Eulerian double-Borel series. -/
noncomputable def eulerianEntireCoeff (n : ℕ) : ℂ :=
  (4 : ℂ) ^ n / ((2 * n + 1).factorial : ℂ)

/-- The Eulerian double-Borel series converges absolutely at every complex
argument.  Its convergence is dominated by the exponential series with
parameter `4 * ‖t‖`, since `n! ≤ (2n+1)!`. -/
theorem eulerianEntireSeries_summable (t : ℂ) :
    Summable (fun n : ℕ => eulerianEntireCoeff n * t ^ n) := by
  have hmajor :
      Summable (fun n : ℕ => (4 * ‖t‖) ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial (4 * ‖t‖)
  apply hmajor.of_norm_bounded
  intro n
  have hfact : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_le (show n ≤ 2 * n + 1 by omega))
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hmain :
      (4 * ‖t‖) ^ n / ((2 * n + 1).factorial : ℝ) ≤
        (4 * ‖t‖) ^ n / (n.factorial : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity) hn hfact
  calc
    ‖eulerianEntireCoeff n * t ^ n‖ =
        (4 * ‖t‖) ^ n / ((2 * n + 1).factorial : ℝ) := by
      simp only [eulerianEntireCoeff, norm_mul, norm_div, norm_pow,
        Complex.norm_natCast]
      norm_num
      rw [mul_pow]
      ring
    _ ≤ _ := hmain

/-- The value of the absolutely convergent Eulerian double-Borel series. -/
noncomputable def eulerianEntireSeries (t : ℂ) : ℂ :=
  ∑' n : ℕ, eulerianEntireCoeff n * t ^ n

/-- At each complex argument the defining series has the asserted sum. -/
theorem eulerianEntireSeries_hasSum (t : ℂ) :
    HasSum (fun n : ℕ => eulerianEntireCoeff n * t ^ n)
      (eulerianEntireSeries t) :=
  (eulerianEntireSeries_summable t).hasSum

/-- The convergent scalar series is a genuine complex-analytic power-series
germ at the origin, with Taylor coefficients equal to the double-Borel
Eulerian coefficients.  This is a statement about an actual function,
not merely an element of the formal power-series ring. -/
theorem eulerianEntireSeries_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt eulerianEntireSeries
      (FormalMultilinearSeries.ofScalars ℂ eulerianEntireCoeff) 0 := by
  apply (hasFPowerSeriesAt_iff).2
  refine Filter.Eventually.of_forall (fun z => ?_)
  simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul, mul_comm] using eulerianEntireSeries_hasSum z

/-- Local complex analyticity of the Eulerian double-Borel output. -/
theorem eulerianEntireSeries_analyticAt_zero :
    AnalyticAt ℂ eulerianEntireSeries 0 :=
  eulerianEntireSeries_hasFPowerSeriesAt_zero.analyticAt

#print axioms EulerianSpecialPoint.eulerianEntireSeries_hasFPowerSeriesAt_zero
#print axioms EulerianSpecialPoint.eulerianEntireSeries_analyticAt_zero

#print axioms EulerianSpecialPoint.eulerianEntireSeries_summable
#print axioms EulerianSpecialPoint.eulerianEntireSeries_hasSum

end EulerianSpecialPoint
