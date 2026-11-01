import GegenbauerFock.MomentSeriesIntegral

/-!
# V007 — exact real exponential closed form for factorial Fock row energies

The Gaussian coherent-section squared coefficient energy at any real u
is the real exponential exp(u²/(4α)). This is the exact infinite series
identity, not a numerical approximation or truncated Taylor series.
-/

namespace GegenbauerFock.FockExponentialSeries

/-- Squared norm of a complex monomial at a real argument. -/
theorem norm_monomial_sq (u : ℝ) (n : ℕ) :
    ‖(u : ℂ) ^ n‖ ^ 2 = (u ^ 2) ^ n := by
  calc
    ‖(u : ℂ) ^ n‖ ^ 2 = (|u| ^ n) ^ 2 := by simp
    _ = (|u| ^ 2) ^ n := by
      calc
        (|u| ^ n) ^ 2 = |u| ^ (n * 2) := by rw [pow_mul]
        _ = |u| ^ (2 * n) := by rw [mul_comm]
        _ = (|u| ^ 2) ^ n := by rw [pow_mul]
    _ = (u ^ 2) ^ n := by rw [sq_abs]

/-- Exact pointwise identification of the nonnegative energy series. -/
theorem energy_series_eq_exp (alpha u : ℝ) :
    (∑' n : ℕ, MomentSeriesIntegral.term alpha n u) =
      Real.exp (u ^ 2 / (4 * alpha)) := by
  have hterm (n : ℕ) :
      MomentSeriesIntegral.term alpha n u =
        (u ^ 2 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ) := by
    unfold MomentSeriesIntegral.term WeightedMoments.squareWeight
    rw [norm_monomial_sq]
    rw [div_pow]
    have hquarter : ((1 / 4 : ℝ) ^ n) = ((4 : ℝ)⁻¹) ^ n := by
      norm_num
    ring_nf
    rw [hquarter]
    ring
  calc
    (∑' n, MomentSeriesIntegral.term alpha n u) =
        ∑' n : ℕ, (u ^ 2 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ) := by
          apply tsum_congr
          exact hterm
    _ = Real.exp (u ^ 2 / (4 * alpha)) := by
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

#print axioms GegenbauerFock.FockExponentialSeries.norm_monomial_sq
#print axioms GegenbauerFock.FockExponentialSeries.energy_series_eq_exp

end GegenbauerFock.FockExponentialSeries
