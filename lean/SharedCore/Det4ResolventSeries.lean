import Mathlib
import SharedCore.Det4LogDeriv

/-! Global convergent spectral resolvent expansion of the actual diagonal
regularized product. This is the scalar diagonal trace formula; no identification
with a concrete Maxwell/Dirac operator is assumed. -/
namespace SharedCore.Det4ResolventSeries
open SharedCore.Det4Zeta SharedCore.Det4Complex SharedCore.Det4Entire
open SharedCore.Det4Zeros SharedCore.Det4LogDeriv
open Filter
open scoped Topology

noncomputable def resolventTerm (z : ℂ) (n : ℕ) : ℂ :=
  (fourthShell n : ℂ) / (1 + shellArgument z n)

noncomputable def spectralLogTerm (z : ℂ) (n : ℕ) : ℂ :=
  -z^3 * resolventTerm z n

noncomputable def diagonalTrace (z : ℂ) : ℂ := ∑' n, resolventTerm z n

theorem one_add_argument_ne (z : ℂ) (n : ℕ) (hz : z ≠ root n) :
    1 + shellArgument z n ≠ 0 := by
  intro h
  apply hz
  unfold root shellArgument at *
  have h' := (div_eq_iff (denominator_ne_zero n)).mp
    (show z / ((n:ℂ)+2) = -1 by linear_combination h)
  linear_combination h'

theorem resolvent_term_rational (z : ℂ) (n : ℕ) (hz : z ≠ root n) :
    resolventTerm z n = ((n:ℂ)+1) / (((n:ℂ)+2)^2 * ((n:ℂ)+2+z)) := by
  have hd : (n:ℂ)+2 ≠ 0 := denominator_ne_zero n
  have ha := one_add_argument_ne z n hz
  have hb : (n:ℂ)+2+z ≠ 0 := by
    intro h
    apply hz
    unfold root
    linear_combination h
  unfold resolventTerm fourthShell shellArgument at *
  push_cast
  field_simp [hd, ha, hb] <;> ring

theorem argument_half_bound (N n : ℕ) (r : ℝ) (z : ℂ)
    (hr : 2*r ≤ (N:ℝ)+2) (hz : ‖z‖ ≤ r) :
    ‖shellArgument z (n+N)‖ ≤ 1/2 := by
  have hc : ((n+N:ℕ):ℂ)+2 = ((n+N+2:ℕ):ℂ) := by push_cast; rfl
  unfold shellArgument
  rw [norm_div, hc, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity)).2
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem resolvent_tail_bound (N n : ℕ) (r : ℝ) (z : ℂ)
    (hr : 2*r ≤ (N:ℝ)+2) (hz : ‖z‖ ≤ r) :
    ‖resolventTerm z (n+N)‖ ≤ 2 * fourthShell (n+N) := by
  have hw := argument_half_bound N n r z hr hz
  have ht := norm_add_le (1 + shellArgument z (n+N)) (-shellArgument z (n+N))
  have ht' : (1:ℝ) ≤ ‖1 + shellArgument z (n+N)‖ + ‖shellArgument z (n+N)‖ := by
    simpa using ht
  have hp : (1/2:ℝ) ≤ ‖1+shellArgument z (n+N)‖ := by linarith
  have hq : 0 ≤ fourthShell (n+N) := by unfold fourthShell; positivity
  unfold resolventTerm
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hq]
  apply (div_le_iff₀ (by linarith)).2
  nlinarith

theorem resolvent_tail_norm_summable (N : ℕ) (r : ℝ) (z : ℂ)
    (hr : 2*r ≤ (N:ℝ)+2) (hz : ‖z‖ ≤ r) :
    Summable (fun n => ‖resolventTerm z (n+N)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => resolvent_tail_bound N n r z hr hz) ((tail_fourth_summable N).mul_left 2)

theorem resolvent_norm_summable (z : ℂ) :
    Summable (fun n => ‖resolventTerm z n‖) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2*‖z‖)
  exact (summable_nat_add_iff N).1 (resolvent_tail_norm_summable N ‖z‖ z (by linarith) le_rfl)

theorem resolvent_summable (z : ℂ) : Summable (resolventTerm z) :=
  (resolvent_norm_summable z).of_norm

theorem spectral_log_summable (z : ℂ) : Summable (spectralLogTerm z) :=
  (resolvent_summable z).mul_left _

theorem resolvent_tail_uniform (N : ℕ) (r : ℝ) (hr : 2*r ≤ (N:ℝ)+2) :
    HasSumUniformlyOn (fun n z => resolventTerm z (n+N))
      (fun z => ∑' n, resolventTerm z (n+N)) {z : ℂ | ‖z‖ ≤ r} :=
  HasSumUniformlyOn.of_norm_le_summable ((tail_fourth_summable N).mul_left 2)
    (fun n z hz => resolvent_tail_bound N n r z hr hz)

theorem spectral_log_tail_bound (N n : ℕ) (r : ℝ) (z : ℂ)
    (hr : 2*r ≤ (N:ℝ)+2) (hz : ‖z‖ ≤ r) :
    ‖spectralLogTerm z (n+N)‖ ≤ (2*r^3) * fourthShell (n+N) := by
  have hq : 0 ≤ fourthShell (n+N) := by unfold fourthShell; positivity
  unfold spectralLogTerm
  rw [norm_mul, norm_neg, norm_pow]
  calc
    _ ≤ r^3 * (2 * fourthShell (n+N)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz 3)
        (resolvent_tail_bound N n r z hr hz) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem spectral_log_tail_uniform (N : ℕ) (r : ℝ) (hr : 2*r ≤ (N:ℝ)+2) :
    HasSumUniformlyOn (fun n z => spectralLogTerm z (n+N))
      (fun z => ∑' n, spectralLogTerm z (n+N)) {z : ℂ | ‖z‖ ≤ r} :=
  HasSumUniformlyOn.of_norm_le_summable ((tail_fourth_summable N).mul_left (2*r^3))
    (fun n z hz => spectral_log_tail_bound N n r z hr hz)

theorem local_log_derivative (w : ℂ) (hw : ‖w‖ < 1) :
    HasDerivAt localLog (-w^3/(1+w)) w := by
  have hsl : 1+w ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have hre := Complex.abs_re_le_norm w
    have hb := neg_abs_le w.re
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hn : 1+w ≠ 0 := by
    intro h
    have he : w = -1 := by linear_combination h
    rw [he] at hw
    norm_num at hw
  have h := hasDerivAt_id w
  have hl := (h.const_add 1).clog hsl
  have hp2 := (h.pow 2).div_const (2:ℂ)
  have hp3 := (h.pow 3).div_const (3:ℂ)
  unfold localLog
  convert ((hl.sub h).add hp2).sub hp3 using 1
  field_simp [hn] <;> ring

theorem shell_log_derivative (z : ℂ) (n : ℕ) (hz : ‖shellArgument z n‖ < 1) :
    HasDerivAt (fun w => shellLog w n) (spectralLogTerm z n) z := by
  have hd := denominator_ne_zero n
  have h := (hasDerivAt_id z).div_const ((n:ℂ)+2)
  have h' := ((local_log_derivative (shellArgument z n) hz).comp z h).const_mul
    (multiplicity n : ℂ)
  unfold shellLog spectralLogTerm resolventTerm shellArgument fourthShell multiplicity at *
  push_cast at *
  convert h' using 1
  field_simp [hd] <;> ring

theorem shell_log_at_zero (n : ℕ) : shellLog 0 n = 0 := by
  simp [shellLog, localLog, shellArgument]

theorem tail_log_derivative (N : ℕ) (r : ℝ) (z : ℂ)
    (hr : 2*r ≤ (N:ℝ)+2) (hz : ‖z‖ < r) :
    HasDerivAt (tailLog N) (∑' n, spectralLogTerm z (n+N)) z := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hu : Summable (fun n => (2*r^3) * fourthShell (n+N)) :=
    (tail_fourth_summable N).mul_left _
  have hg : ∀ n : ℕ, ∀ y ∈ Metric.ball (0:ℂ) r,
      HasDerivAt (fun w => shellLog w (n+N)) (spectralLogTerm y (n+N)) y := by
    intro n y hy
    have hy' : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact shell_log_derivative y (n+N)
      (lt_of_le_of_lt (argument_half_bound N n r y hr hy'.le) (by norm_num))
  have hgb : ∀ n : ℕ, ∀ y ∈ Metric.ball (0:ℂ) r,
      ‖spectralLogTerm y (n+N)‖ ≤ (2*r^3) * fourthShell (n+N) := by
    intro n y hy
    have hy' : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact spectral_log_tail_bound N n r y hr hy'.le
  have h0 : (0:ℂ) ∈ Metric.ball (0:ℂ) r := by simpa using hr0
  have hs0 : Summable (fun n : ℕ => shellLog 0 (n+N)) := by simp [shell_log_at_zero]
  have hzm : z ∈ Metric.ball (0:ℂ) r := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0:ℂ) r).isPreconnected hg hgb h0 hs0 hzm
  apply h.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hzm] with w hw
  have hw' : ‖w‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hw
  exact (tail_series_exchange N w (by linarith)).symm

theorem shell_log_deriv_all (z : ℂ) (n : ℕ) (hz : z ≠ root n) :
    logDeriv (fun w => regularizedShell w n) z = spectralLogTerm z n := by
  have hd := denominator_ne_zero n
  have ha := one_add_argument_ne z n hz
  let a : ℂ → ℂ := fun w => shellArgument w n
  let p : ℂ → ℂ := fun w => -a w + (a w)^2/2 - (a w)^3/3
  have hA : HasDerivAt a (1/((n:ℂ)+2)) z := by
    simpa [a, shellArgument] using (hasDerivAt_id z).div_const ((n:ℂ)+2)
  have hP := (hA.neg.add ((hA.pow 2).div_const (2:ℂ))).sub
    ((hA.pow 3).div_const (3:ℂ))
  have hE := hP.cexp
  have hB := (hA.const_add 1).mul hE
  unfold regularizedShell
  rw [logDeriv_fun_pow (f := fun w => (1+a w)*Complex.exp (p w)) (by
    exact hB.differentiableAt)]
  have hM := logDeriv_mul (f := fun w => 1+a w) (g := fun w => Complex.exp (p w)) z
    ha (Complex.exp_ne_zero _) (hA.const_add 1).differentiableAt hE.differentiableAt
  rw [hM, logDeriv_apply, logDeriv_apply, (hA.const_add 1).deriv, hE.deriv]
  unfold p a spectralLogTerm resolventTerm fourthShell multiplicity shellArgument
  push_cast
  field_simp [hd, ha, Complex.exp_ne_zero] <;> ring

theorem global_spectral_log_derivative (z : ℂ) (hz : ∀ n : ℕ, z ≠ root n) :
    determinantLogDeriv z = ∑' n, spectralLogTerm z n := by
  let r : ℝ := ‖z‖+1
  obtain ⟨N,hN⟩ := exists_nat_gt (2*r)
  have hr : 2*r ≤ (N:ℝ)+2 := by linarith
  have hzR : ‖z‖ < r := by dsimp [r]; linarith
  have hzN : ‖z‖ < (N:ℝ)+2 := by dsimp [r] at *; linarith [norm_nonneg z]
  let head : ℂ → ℂ := fun w => ∏ n ∈ Finset.range N, regularizedShell w n
  let tail : ℂ → ℂ := fun w => Complex.exp (tailLog N w)
  have hEq : regularizedProduct =ᶠ[𝓝 z] head * tail := by
    have hopen : IsOpen {w : ℂ | ‖w‖ < (N:ℝ)+2} :=
      isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen.mem_nhds hzN] with w hw
    exact product_factorization N w hw
  have hhead : head z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun n _ => fun h => hz n ((shell_eq_zero_iff z n).mp h))
  have htail := (tail_log_derivative N r z hr hzR).cexp
  have hM := logDeriv_mul (f := head) (g := tail) z hhead (Complex.exp_ne_zero _)
    (finite_head_analytic N z).differentiableAt htail.differentiableAt
  have hh : logDeriv head z = ∑ n ∈ Finset.range N, spectralLogTerm z n := by
    unfold head
    rw [logDeriv_fun_prod (fun n _ => fun h => hz n ((shell_eq_zero_iff z n).mp h))
      (fun n _ => (shell_analytic n z).differentiableAt)]
    exact Finset.sum_congr rfl (fun n _ => shell_log_deriv_all z n (hz n))
  have ht : logDeriv tail z = ∑' n, spectralLogTerm z (n+N) := by
    unfold tail
    rw [logDeriv_apply, htail.deriv]
    field_simp [Complex.exp_ne_zero] <;> ring
  unfold determinantLogDeriv
  rw [(logDeriv_congr_nhds hEq).eq_of_nhds, hM, hh, ht]
  exact (spectral_log_summable z).sum_add_tsum_nat_add N

theorem determinant_resolvent_trace (z : ℂ) (hz : ∀ n : ℕ, z ≠ root n) :
    determinantLogDeriv z = -z^3 * diagonalTrace z := by
  rw [global_spectral_log_derivative z hz]
  unfold spectralLogTerm diagonalTrace
  rw [tsum_mul_left]

theorem determinant_resolvent_rational_series (z : ℂ) (hz : ∀ n : ℕ, z ≠ root n) :
    determinantLogDeriv z = -z^3 *
      (∑' n : ℕ, ((n:ℂ)+1) / (((n:ℂ)+2)^2 * ((n:ℂ)+2+z))) := by
  rw [determinant_resolvent_trace z hz]
  unfold diagonalTrace
  simp_rw [resolvent_term_rational z _ (hz _)]

theorem diagonal_trace_at_zero : diagonalTrace 0 = riemannZeta 2 - riemannZeta 3 := by
  unfold diagonalTrace resolventTerm shellArgument
  simp only [zero_div, add_zero, div_one]
  rw [← Complex.ofReal_tsum, fourth_moment_identification,
      moment_riemannZeta_difference 4 (by norm_num)]
  norm_num

end SharedCore.Det4ResolventSeries

#print axioms SharedCore.Det4ResolventSeries.one_add_argument_ne
#print axioms SharedCore.Det4ResolventSeries.resolvent_term_rational
#print axioms SharedCore.Det4ResolventSeries.argument_half_bound
#print axioms SharedCore.Det4ResolventSeries.resolvent_tail_bound
#print axioms SharedCore.Det4ResolventSeries.resolvent_tail_norm_summable
#print axioms SharedCore.Det4ResolventSeries.resolvent_norm_summable
#print axioms SharedCore.Det4ResolventSeries.resolvent_summable
#print axioms SharedCore.Det4ResolventSeries.spectral_log_summable
#print axioms SharedCore.Det4ResolventSeries.resolvent_tail_uniform
#print axioms SharedCore.Det4ResolventSeries.spectral_log_tail_bound
#print axioms SharedCore.Det4ResolventSeries.spectral_log_tail_uniform
#print axioms SharedCore.Det4ResolventSeries.local_log_derivative
#print axioms SharedCore.Det4ResolventSeries.shell_log_derivative
#print axioms SharedCore.Det4ResolventSeries.shell_log_at_zero
#print axioms SharedCore.Det4ResolventSeries.tail_log_derivative
#print axioms SharedCore.Det4ResolventSeries.shell_log_deriv_all
#print axioms SharedCore.Det4ResolventSeries.global_spectral_log_derivative
#print axioms SharedCore.Det4ResolventSeries.determinant_resolvent_trace
#print axioms SharedCore.Det4ResolventSeries.determinant_resolvent_rational_series
#print axioms SharedCore.Det4ResolventSeries.diagonal_trace_at_zero
