import Mathlib
import SharedCore.Det4ComplexProduct

/-! Analytic germ of the actual diagonal regularized product, with
fourth derivative checked through the certified complex series. -/
namespace SharedCore.Det4Derivative
open SharedCore.Det4Zeta SharedCore.Det4Complex
open Filter
open scoped Topology NNReal

noncomputable def reducedCoeff (k : ℕ) : ℂ :=
  coefficient 1 k * (powerMoment k : ℂ)

noncomputable def reduced (z : ℂ) : ℂ :=
  FormalMultilinearSeries.ofScalarsSum reducedCoeff z

theorem reduced_coeff_norm (k : ℕ) :
    ‖reducedCoeff k‖ = taylorMajorant 1 k := by
  have hcast : (k:ℂ)+4 = ((k+4:ℕ):ℂ) := by push_cast; rfl
  unfold reducedCoeff coefficient taylorMajorant
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_pow, one_mul, hcast, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (power_moment_nonneg k)]
  push_cast
  ring

theorem reduced_coeff_summable_norm :
    Summable (fun k => ‖reducedCoeff k‖) := by
  simp_rw [reduced_coeff_norm]
  exact taylor_majorant_summable 1 (by norm_num) (by norm_num)

theorem reduced_series_radius :
    (1 : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ reducedCoeff).radius := by
  have hs : Summable (fun k => ‖FormalMultilinearSeries.ofScalars ℂ reducedCoeff k‖ *
      ((1 : ℝ≥0) : ℝ)^k) := by
    simpa [FormalMultilinearSeries.ofScalars_norm] using reduced_coeff_summable_norm
  simpa using (FormalMultilinearSeries.ofScalars ℂ reducedCoeff).le_radius_of_summable_norm hs

theorem reduced_analytic : AnalyticAt ℂ reduced 0 := by
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ reducedCoeff).radius :=
    lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) reduced_series_radius
  exact ((FormalMultilinearSeries.ofScalars ℂ reducedCoeff).hasFPowerSeriesOnBall hpos).analyticAt

theorem global_log_factor (z : ℂ) : globalLog z = z^4 * reduced z := by
  unfold globalLog reduced
  rw [FormalMultilinearSeries.ofScalars_sum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold reducedCoeff coefficient
  simp only [one_pow, mul_one, smul_eq_mul, pow_add]
  ring

theorem reduced_at_zero :
    reduced 0 = -(riemannZeta 2 - riemannZeta 3)/4 := by
  unfold reduced
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  simpa [reducedCoeff, coefficient, smul_eq_mul] using fourth_coefficient

theorem global_log_zero : globalLog 0 = 0 := by
  rw [global_log_factor]
  simp

theorem global_log_analytic : AnalyticAt ℂ globalLog 0 := by
  have h : globalLog = fun z => z^4 * reduced z := funext global_log_factor
  rw [h]
  exact (show AnalyticAt ℂ (fun z : ℂ => z^4) 0 by fun_prop).mul reduced_analytic

theorem exp_quadratic_factor :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E 0 ∧
      ∀ z : ℂ, Complex.exp z = 1 + z + z^2 * E z := by
  have h : AnalyticAt ℂ Complex.exp 0 := by fun_prop
  obtain ⟨E, hE, he⟩ := h.exists_eq_sum_add_pow_mul 2
  refine ⟨E, hE, fun z => ?_⟩
  simpa [Finset.sum_range_succ, iteratedDeriv_one, Complex.deriv_exp, smul_eq_mul] using he z

theorem determinant_analytic_factor :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧
      K 0 = -(riemannZeta 2 - riemannZeta 3)/4 ∧
      regularizedProduct =ᶠ[𝓝 0] (fun z => 1 + z^4 * K z) := by
  obtain ⟨E,hE,he⟩ := exp_quadratic_factor
  let K : ℂ → ℂ := fun z => reduced z + z^4 * reduced z^2 * E (globalLog z)
  have hE' : AnalyticAt ℂ E (globalLog 0) := by
    rw [global_log_zero]
    exact hE
  have hcomp : AnalyticAt ℂ (fun z => E (globalLog z)) 0 :=
    hE'.comp global_log_analytic
  have hK : AnalyticAt ℂ K 0 := by
    dsimp [K]
    exact reduced_analytic.add (((show AnalyticAt ℂ (fun z : ℂ => z^4) 0 by fun_prop).mul
      (reduced_analytic.pow 2)).mul hcomp)
  refine ⟨K,hK,?_,?_⟩
  · simp [K, reduced_at_zero]
  · filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<2)] with z hz
    have hz' : ‖z‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    rw [regularized_product_eq_exp z hz', he (globalLog z)]
    dsimp [K]
    rw [global_log_factor z]
    ring

theorem determinant_analytic_at_zero : AnalyticAt ℂ regularizedProduct 0 := by
  obtain ⟨K,hK,_,he⟩ := determinant_analytic_factor
  have h : AnalyticAt ℂ (fun z => 1 + z^4 * K z) 0 :=
    analyticAt_const.add ((show AnalyticAt ℂ (fun z : ℂ => z^4) 0 by fun_prop).mul hK)
  exact h.congr he.symm

theorem determinant_value_at_zero : regularizedProduct 0 = 1 := by
  rw [regularized_product_eq_exp 0 (by norm_num), global_log_zero, Complex.exp_zero]

theorem determinant_derivatives (k : ℕ) (hk : 0 < k) (hk4 : k ≤ 4) :
    iteratedDeriv k regularizedProduct 0 =
      if k = 4 then -6*(riemannZeta 2 - riemannZeta 3) else 0 := by
  obtain ⟨K,hK,hK0,he⟩ := determinant_analytic_factor
  rw [he.iteratedDeriv_eq k, iteratedDeriv_const_add hk]
  have hpow : ContDiffAt ℂ (k : ℕ∞) (fun z : ℂ => z^4) 0 := by fun_prop
  have hKd : ContDiffAt ℂ (k : ℕ∞) K 0 := hK.contDiffAt
  change iteratedDeriv k ((fun z : ℂ => z^4) * K) 0 = _
  rw [iteratedDeriv_mul hpow hKd]
  interval_cases k <;>
    simp [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, hK0] <;> ring

theorem determinant_fourth_derivative :
    iteratedDeriv 4 regularizedProduct 0 = -6*(riemannZeta 2 - riemannZeta 3) := by
  simpa using determinant_derivatives 4 (by norm_num) (by norm_num)

theorem log_fourth_derivative :
    iteratedDeriv 4 globalLog 0 = -6*(riemannZeta 2 - riemannZeta 3) := by
  have he : globalLog = (fun z : ℂ => z^4) * reduced := funext global_log_factor
  rw [he]
  have hp : ContDiffAt ℂ 4 (fun z : ℂ => z^4) 0 := by fun_prop
  rw [iteratedDeriv_mul hp reduced_analytic.contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, reduced_at_zero] <;> ring

end SharedCore.Det4Derivative

#print axioms SharedCore.Det4Derivative.reduced_coeff_norm
#print axioms SharedCore.Det4Derivative.reduced_coeff_summable_norm
#print axioms SharedCore.Det4Derivative.reduced_series_radius
#print axioms SharedCore.Det4Derivative.reduced_analytic
#print axioms SharedCore.Det4Derivative.global_log_factor
#print axioms SharedCore.Det4Derivative.reduced_at_zero
#print axioms SharedCore.Det4Derivative.global_log_zero
#print axioms SharedCore.Det4Derivative.global_log_analytic
#print axioms SharedCore.Det4Derivative.exp_quadratic_factor
#print axioms SharedCore.Det4Derivative.determinant_analytic_factor
#print axioms SharedCore.Det4Derivative.determinant_analytic_at_zero
#print axioms SharedCore.Det4Derivative.determinant_value_at_zero
#print axioms SharedCore.Det4Derivative.determinant_derivatives
#print axioms SharedCore.Det4Derivative.determinant_fourth_derivative
#print axioms SharedCore.Det4Derivative.log_fourth_derivative
