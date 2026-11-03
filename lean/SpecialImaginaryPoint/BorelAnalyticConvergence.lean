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

/-!
The following strengthens convergence at each parameter to a formal
infinite radius of convergence and hence analyticity everywhere.
-/ 

/-- The complex scalar Taylor expansion of the Eulerian Borel output
has infinite radius of convergence. -/
theorem eulerianEntireSeries_radius_top :
    (FormalMultilinearSeries.ofScalars ℂ eulerianEntireCoeff).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hmajor :
      Summable (fun n : ℕ => (4 * (r : ℝ)) ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial (4 * (r : ℝ))
  simp only [FormalMultilinearSeries.ofScalars_norm]
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hmajor
  intro n
  have hfact : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_le (show n ≤ 2 * n + 1 by omega))
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hmain :
      (4 * (r : ℝ)) ^ n / ((2 * n + 1).factorial : ℝ) ≤
        (4 * (r : ℝ)) ^ n / (n.factorial : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity) hn hfact
  calc
    ‖eulerianEntireCoeff n‖ * (r : ℝ) ^ n =
        (4 * (r : ℝ)) ^ n / ((2 * n + 1).factorial : ℝ) := by
      simp only [eulerianEntireCoeff, norm_div, norm_pow,
        Complex.norm_natCast]
      norm_num
      rw [mul_pow]
      ring
    _ ≤ _ := hmain

/-- The genuine Eulerian double-Borel function has the specified Taylor
expansion on the entire complex plane (infinite analytic radius). -/
theorem eulerianEntireSeries_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall eulerianEntireSeries
      (FormalMultilinearSeries.ofScalars ℂ eulerianEntireCoeff) 0 ⊤ := by
  refine ⟨by rw [eulerianEntireSeries_radius_top], by simp, ?_⟩
  intro y hy
  simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] using eulerianEntireSeries_hasSum y

/-- Global holomorphy of the Eulerian double-Borel series. -/
theorem eulerianEntireSeries_analyticAt (z : ℂ) :
    AnalyticAt ℂ eulerianEntireSeries z := by
  exact eulerianEntireSeries_hasFPowerSeriesOnBall.analyticAt_of_mem (by simp)

/-!
## A pointwise analytic derivative and the exact scalar ODE recurrence

The coefficient recurrence below is the Taylor-coefficient form of
the second-order ODE t F''(t) + (3/2) F'(t) - F(t) = 0.
The separate analytic differential equation is not claimed here.
-/

/-- The exact factorial recurrence for the Taylor coefficients
of the Eulerian entire double-Borel output. -/
theorem eulerianEntireCoeff_recurrence (n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + 3 / 2) *
      eulerianEntireCoeff (n + 1) = eulerianEntireCoeff n := by
  have hindex : 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 := by omega
  have hfac :
      (2 * (n + 1) + 1).factorial =
        (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
    rw [hindex, Nat.factorial_succ, Nat.factorial_succ]
    ring
  unfold eulerianEntireCoeff
  rw [hfac, pow_succ]
  push_cast
  have hbase : ((2 * n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (2 * n + 1)))
  have htwo : ((2 * n + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < 2 * n + 2 by omega))
  have hthree : ((2 * n + 3 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < 2 * n + 3 by omega))
  field_simp
  have hden : (3 + (n : ℂ) * 2) ≠ 0 := by
    have heq : (3 + (n : ℂ) * 2) = ((2 * n + 3 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact hthree
  calc
    _ = (4 * (3 + (n : ℂ) * 2)) *
          (3 + (n : ℂ) * 2)⁻¹ := by ring
    _ = 4 := by
      rw [mul_assoc, mul_inv_cancel₀ hden, mul_one]

/-- The actual analytic Eulerian series takes the expected value at zero. -/
theorem eulerianEntireSeries_zero : eulerianEntireSeries 0 = 1 := by
  unfold eulerianEntireSeries
  rw [tsum_eq_single 0]
  · norm_num [eulerianEntireCoeff]
  · intro n hn
    cases n with
    | zero => contradiction
    | succ n => simp

/-- Derivative of the *actual analytic function* at the origin, derived
from its certified Taylor expansion rather than only formal coefficients. -/
theorem eulerianEntireSeries_deriv_zero :
    deriv eulerianEntireSeries 0 = (2 / 3 : ℂ) := by
  rw [eulerianEntireSeries_hasFPowerSeriesAt_zero.deriv]
  norm_num [FormalMultilinearSeries.ofScalars_apply_eq,
    eulerianEntireCoeff]

#print axioms EulerianSpecialPoint.eulerianEntireCoeff_recurrence
#print axioms EulerianSpecialPoint.eulerianEntireSeries_zero
#print axioms EulerianSpecialPoint.eulerianEntireSeries_deriv_zero

#print axioms EulerianSpecialPoint.eulerianEntireSeries_radius_top
#print axioms EulerianSpecialPoint.eulerianEntireSeries_hasFPowerSeriesOnBall
#print axioms EulerianSpecialPoint.eulerianEntireSeries_analyticAt

#print axioms EulerianSpecialPoint.eulerianEntireSeries_hasFPowerSeriesAt_zero
#print axioms EulerianSpecialPoint.eulerianEntireSeries_analyticAt_zero

#print axioms EulerianSpecialPoint.eulerianEntireSeries_summable
#print axioms EulerianSpecialPoint.eulerianEntireSeries_hasSum

end EulerianSpecialPoint
