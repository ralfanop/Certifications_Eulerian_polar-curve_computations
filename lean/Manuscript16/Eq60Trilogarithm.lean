import Mathlib
import SharedCore.Det4ZetaMoments

/-! Manuscript 16.6 (18 Nov 2026), equation (60), p. 19.
The real trilogarithm on [0,1] is defined by its convergent defining series.
No numerical approximation or assumed integration identity is used. -/
namespace Manuscript16.Eq60
open SharedCore.Det4Zeta
open MeasureTheory Set Filter
open scoped Topology BigOperators Interval

noncomputable def reciprocalTerm (n : ℕ) : ℝ :=
  1 / (((n : ℝ)+1)^4 + ((n : ℝ)+1)^3)

noncomputable def trilogTerm (n : ℕ) (x : ℝ) : ℝ :=
  x^(n+1) / ((n : ℝ)+1)^3

noncomputable def trilogarithm (x : ℝ) : ℝ := ∑' n, trilogTerm n x

theorem partial_fraction (n : ℕ) :
    reciprocalTerm n + zetaTerm 2 n - zetaTerm 3 n =
    1 / ((n:ℝ)+1) - 1 / ((n:ℝ)+2) := by
  unfold reciprocalTerm zetaTerm
  rw [Real.rpow_two, show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast]
  have h : 0 < (n:ℝ)+1 := by positivity
  have h' : 0 < (n:ℝ)+2 := by positivity
  have h'' : 0 < ((n:ℝ)+1)^4 + ((n:ℝ)+1)^3 := by positivity
  field_simp [ne_of_gt h, ne_of_gt h', ne_of_gt h''] <;> ring

theorem reciprocal_summable : Summable reciprocalTerm := by
  refine Summable.of_nonneg_of_le (fun n => by unfold reciprocalTerm; positivity) ?_
    (zeta_term_summable 3 (by norm_num))
  intro n
  unfold reciprocalTerm zetaTerm
  rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [pow_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) 4]

theorem telescoping_partial (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / ((n:ℝ)+1) - 1 / ((n:ℝ)+2))) =
      1 - 1 / ((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem complement_real :
    1 - (∑' n, reciprocalTerm n) = zetaSeries 2 - zetaSeries 3 := by
  have h2 := zeta_term_summable 2 (by norm_num)
  have h3 := zeta_term_summable 3 (by norm_num)
  have h := ((reciprocal_summable.hasSum.add h2.hasSum).sub h3.hasSum).tendsto_sum_nat
  have he : (fun N : ℕ => ∑ n ∈ Finset.range N,
      (reciprocalTerm n + zetaTerm 2 n - zetaTerm 3 n)) =
      (fun N : ℕ => 1 - 1 / ((N:ℝ)+1)) := by
    funext N
    simp_rw [partial_fraction]
    exact telescoping_partial N
  rw [he] at h
  have hlim : Tendsto (fun N : ℕ => (1:ℝ) - 1 / ((N:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hh := tendsto_nhds_unique h hlim
  unfold zetaSeries
  linarith

theorem trilog_term_bound (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    ‖trilogTerm n x‖ ≤ zetaTerm 3 n := by
  unfold trilogTerm zetaTerm
  rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast]
  have hx0 : 0 ≤ x := hx.1
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ x^(n+1) / ((n:ℝ)+1)^3)]
  exact div_le_div_of_nonneg_right
    (by simpa using pow_le_pow_left₀ hx.1 hx.2 (n+1)) (by positivity)

theorem trilog_uniform :
    HasSumUniformlyOn trilogTerm trilogarithm (Icc (0:ℝ) 1) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    (zeta_term_summable 3 (by norm_num)) (fun n x hx => trilog_term_bound n x hx)

theorem integral_term (n : ℕ) :
    (∫ x in (0:ℝ)..1, trilogTerm n x) = reciprocalTerm n := by
  unfold trilogTerm reciprocalTerm
  rw [intervalIntegral.integral_div, intervalIntegral.integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one]
  have h : 0 < (n:ℝ)+1 := by positivity
  have h' : 0 < (n:ℝ)+1+1 := by positivity
  have h'' : 0 < ((n:ℝ)+1)^4+((n:ℝ)+1)^3 := by positivity
  field_simp [ne_of_gt h, ne_of_gt h', ne_of_gt h''] <;> ring

theorem integral_trilogarithm :
    (∫ x in (0:ℝ)..1, trilogarithm x) = ∑' n, reciprocalTerm n := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hInt (n : ℕ) : Integrable (trilogTerm n) (volume.restrict (Ioc (0:ℝ) 1)) := by
    have hc : Continuous (trilogTerm n) := by unfold trilogTerm; fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).1
      (hc.intervalIntegrable 0 1)
  have hNorm (n : ℕ) :
      (∫ x in Ioc (0:ℝ) 1, ‖trilogTerm n x‖) = reciprocalTerm n := by
    calc
      _ = ∫ x in Ioc (0:ℝ) 1, trilogTerm n x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
        have hx' : 0 ≤ x := le_of_lt hx.1
        rw [Real.norm_of_nonneg (by unfold trilogTerm; positivity)]
      _ = _ := by rw [← intervalIntegral.integral_of_le h01]; exact integral_term n
  have hs : Summable (fun n : ℕ => ∫ x in Ioc (0:ℝ) 1, ‖trilogTerm n x‖) := by
    simp_rw [hNorm]
    exact reciprocal_summable
  rw [intervalIntegral.integral_of_le h01]
  unfold trilogarithm
  rw [← integral_tsum_of_summable_integral_norm hInt hs]
  apply tsum_congr
  intro n
  rw [← intervalIntegral.integral_of_le h01]
  exact integral_term n

theorem eq60_series :
    (1:ℂ) - ((∑' n, reciprocalTerm n : ℝ):ℂ) =
      riemannZeta 2 - riemannZeta 3 := by
  have h2 := real_zeta_series_eq_riemannZeta 2 (by norm_num)
  have h3 := real_zeta_series_eq_riemannZeta 3 (by norm_num)
  norm_num at h2 h3
  calc
    _ = ((1 - (∑' n, reciprocalTerm n) : ℝ):ℂ) := by push_cast <;> rfl
    _ = ((zetaSeries 2 - zetaSeries 3 : ℝ):ℂ) := congrArg Complex.ofReal complement_real
    _ = _ := by rw [Complex.ofReal_sub, h2, h3]

theorem eq60_integral :
    (1:ℂ) - ((∫ x in (0:ℝ)..1, trilogarithm x : ℝ):ℂ) =
      riemannZeta 2 - riemannZeta 3 := by
  rw [integral_trilogarithm]
  exact eq60_series

theorem eq60_chain :
    (riemannZeta 2 - riemannZeta 3 =
      1 - ((∫ x in (0:ℝ)..1, trilogarithm x : ℝ):ℂ)) ∧
    (1 - ((∫ x in (0:ℝ)..1, trilogarithm x : ℝ):ℂ) =
      1 - ((∑' n, reciprocalTerm n : ℝ):ℂ)) := by
  exact ⟨eq60_integral.symm, eq60_integral.trans eq60_series.symm⟩

end Manuscript16.Eq60

#print axioms Manuscript16.Eq60.partial_fraction
#print axioms Manuscript16.Eq60.reciprocal_summable
#print axioms Manuscript16.Eq60.telescoping_partial
#print axioms Manuscript16.Eq60.complement_real
#print axioms Manuscript16.Eq60.trilog_term_bound
#print axioms Manuscript16.Eq60.trilog_uniform
#print axioms Manuscript16.Eq60.integral_term
#print axioms Manuscript16.Eq60.integral_trilogarithm
#print axioms Manuscript16.Eq60.eq60_series
#print axioms Manuscript16.Eq60.eq60_integral
#print axioms Manuscript16.Eq60.eq60_chain
