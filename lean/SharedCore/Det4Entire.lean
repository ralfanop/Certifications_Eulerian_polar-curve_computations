import Mathlib
import SharedCore.Det4ComplexProduct

/-! Entire extension of the actual diagonal regularized product.
The finite head accounts for possible zeros; logarithms are used only in the tail. -/
namespace SharedCore.Det4Entire
open SharedCore.Det4Zeta SharedCore.Det4Complex
open Filter
open scoped Topology NNReal ENNReal

noncomputable def tailMoment (N k : ℕ) : ℝ :=
  ∑' n : ℕ, powerShell k (n+N)
noncomputable def tailFourth (N : ℕ) : ℝ :=
  ∑' n : ℕ, fourthShell (n+N)

theorem tail_fourth_summable (N : ℕ) : Summable (fun n => fourthShell (n+N)) :=
  (summable_nat_add_iff N).2 fourth_shell_summable

theorem tail_power_summable (N k : ℕ) : Summable (fun n => powerShell k (n+N)) :=
  (summable_nat_add_iff N).2 (power_shell_summable k)

theorem tail_moment_nonneg (N k : ℕ) : 0 ≤ tailMoment N k := by
  unfold tailMoment
  exact tsum_nonneg (fun n => by unfold powerShell fourthShell; positivity)

theorem tail_fourth_nonneg (N : ℕ) : 0 ≤ tailFourth N := by
  unfold tailFourth
  exact tsum_nonneg (fun n => by unfold fourthShell; positivity)

theorem tail_power_bound (N k n : ℕ) :
    powerShell k (n+N) ≤ (1/((N:ℝ)+2))^k * fourthShell (n+N) := by
  have hb : 1 / (((n+N:ℕ):ℝ)+2) ≤ 1/((N:ℝ)+2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold powerShell
  rw [mul_comm ((1/((N:ℝ)+2))^k)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb k)
    (by unfold fourthShell; positivity)

theorem tail_moment_bound (N k : ℕ) :
    tailMoment N k ≤ (1/((N:ℝ)+2))^k * tailFourth N := by
  unfold tailMoment tailFourth
  rw [← tsum_mul_left]
  exact (tail_power_summable N k).tsum_le_tsum (tail_power_bound N k)
    ((tail_fourth_summable N).mul_left _)

noncomputable def tailMajorant (N : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  r^k * tailMoment N k / ((k:ℝ)+4)

theorem tail_majorant_bound (N : ℕ) (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    tailMajorant N r k ≤ (tailFourth N / 4) * (r/((N:ℝ)+2))^k := by
  have hA := tail_fourth_nonneg N
  have hnum : 0 ≤ r^k * ((1/((N:ℝ)+2))^k * tailFourth N) := by positivity
  unfold tailMajorant
  calc
    _ ≤ r^k * ((1/((N:ℝ)+2))^k * tailFourth N) / ((k:ℝ)+4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tail_moment_bound N k)
        (pow_nonneg hr k)) (by positivity)
    _ ≤ r^k * ((1/((N:ℝ)+2))^k * tailFourth N) / 4 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = _ := by rw [div_pow, div_pow, one_pow]; ring

theorem tail_majorant_summable (N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hrN : r < (N:ℝ)+2) : Summable (tailMajorant N r) := by
  have hg : Summable (fun k : ℕ => (r/((N:ℝ)+2))^k) :=
    summable_geometric_of_lt_one (by positivity) ((div_lt_one (by positivity)).2 hrN)
  have hnonneg (k : ℕ) : 0 ≤ tailMajorant N r k := by
    unfold tailMajorant
    exact div_nonneg (mul_nonneg (pow_nonneg hr _) (tail_moment_nonneg N k)) (by positivity)
  exact Summable.of_nonneg_of_le hnonneg
    (tail_majorant_bound N r hr) (hg.mul_left _)

noncomputable def tailJoint (N : ℕ) (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  joint z (p.1,p.2+N)

theorem tail_joint_norm_summable (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    Summable (fun p : ℕ × ℕ => ‖tailJoint N z p‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (tailJoint N z p))).mpr
  constructor
  · intro k
    simp_rw [tailJoint, joint_norm]
    exact (tail_power_summable N k).mul_left _
  · have he (k : ℕ) : (∑' n : ℕ, ‖tailJoint N z (k,n)‖) =
        ‖z‖^4 * tailMajorant N ‖z‖ k := by
      simp_rw [tailJoint, joint_norm]
      rw [tsum_mul_left, pow_add]
      unfold tailMajorant tailMoment
      ring
    simp_rw [he]
    exact (tail_majorant_summable N ‖z‖ (norm_nonneg z) hz).mul_left _

theorem tail_joint_summable (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    Summable (tailJoint N z) :=
  (tail_joint_norm_summable N z hz).of_norm

theorem tail_joint_inner_moment (N : ℕ) (z : ℂ) (k : ℕ) :
    (∑' n : ℕ, tailJoint N z (k,n)) = coefficient z k * (tailMoment N k : ℂ) := by
  simp only [tailJoint, joint]
  rw [tsum_mul_left]
  unfold tailMoment
  rw [Complex.ofReal_tsum]

theorem tail_argument_norm (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) (n : ℕ) :
    ‖shellArgument z (n+N)‖ < 1 := by
  have hc : ((n+N:ℕ):ℂ)+2 = ((n+N+2:ℕ):ℂ) := by push_cast; rfl
  unfold shellArgument
  rw [norm_div, hc, Complex.norm_natCast]
  apply (div_lt_one (by positivity)).2
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem tail_joint_inner_shell (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) (n : ℕ) :
    (∑' k : ℕ, tailJoint N z (k,n)) = shellLog z (n+N) := by
  simp_rw [tailJoint, joint_as_local]
  rw [tsum_mul_left]
  unfold shellLog
  rw [(local_log_hasSum _ (tail_argument_norm N z hz n)).tsum_eq]

noncomputable def tailLog (N : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, coefficient z k * (tailMoment N k : ℂ)

theorem tail_series_exchange (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    (∑' n : ℕ, shellLog z (n+N)) = tailLog N z := by
  unfold tailLog
  simp_rw [← tail_joint_inner_shell N z hz, ← tail_joint_inner_moment N z]
  exact Summable.tsum_comm (f := fun k n => tailJoint N z (k,n)) (tail_joint_summable N z hz)

theorem tail_log_hasSum (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    HasSum (fun n : ℕ => shellLog z (n+N)) (tailLog N z) := by
  have h := (tail_joint_summable N z hz).prod_symm.prod
  have hs : Summable (fun n : ℕ => shellLog z (n+N)) := by
    convert h using 1
    funext n
    exact (tail_joint_inner_shell N z hz n).symm
  rw [← tail_series_exchange N z hz]
  exact hs.hasSum

theorem tail_exp_shell (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) (n : ℕ) :
    Complex.exp (shellLog z (n+N)) = regularizedShell z (n+N) := by
  have hnorm := tail_argument_norm N z hz n
  have hne : 1 + shellArgument z (n+N) ≠ 0 := by
    intro h
    have he : shellArgument z (n+N) = -1 := by linear_combination h
    rw [he] at hnorm
    norm_num at hnorm
  unfold shellLog regularizedShell localLog
  rw [Complex.exp_nat_mul]
  congr 1
  rw [show Complex.log (1+shellArgument z (n+N)) - shellArgument z (n+N) +
        shellArgument z (n+N)^2/2 - shellArgument z (n+N)^3/3 =
       Complex.log (1+shellArgument z (n+N)) +
        (-shellArgument z (n+N)+shellArgument z (n+N)^2/2-shellArgument z (n+N)^3/3) by ring,
      Complex.exp_add, Complex.exp_log hne]

theorem tail_product_hasProd (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    HasProd (fun n : ℕ => regularizedShell z (n+N)) (Complex.exp (tailLog N z)) := by
  have h := (tail_log_hasSum N z hz).cexp
  convert h using 1
  funext n
  exact (tail_exp_shell N z hz n).symm

theorem full_product_hasProd (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    HasProd (regularizedShell z)
      ((∏ n ∈ Finset.range N, regularizedShell z n) * Complex.exp (tailLog N z)) :=
  (tail_product_hasProd N z hz).prod_range_mul

theorem product_factorization (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    regularizedProduct z =
      (∏ n ∈ Finset.range N, regularizedShell z n) * Complex.exp (tailLog N z) :=
  (full_product_hasProd N z hz).tprod_eq

theorem product_multipliable_everywhere (z : ℂ) : Multipliable (regularizedShell z) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  exact (full_product_hasProd N z (by linarith)).multipliable

noncomputable def tailCoeff (N k : ℕ) : ℂ :=
  coefficient 1 k * (tailMoment N k : ℂ)

noncomputable def tailReduced (N : ℕ) (z : ℂ) : ℂ :=
  FormalMultilinearSeries.ofScalarsSum (tailCoeff N) z

theorem tail_coeff_norm (N k : ℕ) :
    ‖tailCoeff N k‖ = tailMajorant N 1 k := by
  have hcast : (k:ℂ)+4 = ((k+4:ℕ):ℂ) := by push_cast; rfl
  unfold tailCoeff coefficient tailMajorant
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_pow, one_mul, hcast, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (tail_moment_nonneg N k)]
  push_cast
  simp only [one_pow, one_mul]
  ring

theorem tail_series_radius (N : ℕ) (r : ℝ≥0) (hr : (r:ℝ) < (N:ℝ)+2) :
    (r : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ (tailCoeff N)).radius := by
  have hs : Summable (fun k => ‖FormalMultilinearSeries.ofScalars ℂ (tailCoeff N) k‖ *
      (r:ℝ)^k) := by
    simp_rw [FormalMultilinearSeries.ofScalars_norm, tail_coeff_norm]
    convert tail_majorant_summable N (r:ℝ) r.coe_nonneg hr using 1
    funext k
    unfold tailMajorant
    simp only [one_pow, one_mul]
    ring
  exact (FormalMultilinearSeries.ofScalars ℂ (tailCoeff N)).le_radius_of_summable_norm hs

theorem tail_log_factor (N : ℕ) (z : ℂ) : tailLog N z = z^4 * tailReduced N z := by
  unfold tailLog tailReduced
  rw [FormalMultilinearSeries.ofScalars_sum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold tailCoeff coefficient
  simp only [one_pow, mul_one, smul_eq_mul, pow_add]
  ring

theorem tail_reduced_analytic (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    AnalyticAt ℂ (tailReduced N) z := by
  let r : ℝ≥0 := ⟨(‖z‖+((N:ℝ)+2))/2, by positivity⟩
  have hr : (r:ℝ) < (N:ℝ)+2 := by
    change (‖z‖+((N:ℝ)+2))/2 < (N:ℝ)+2
    linarith
  have hzR : ‖z‖ < (r:ℝ) := by
    change ‖z‖ < (‖z‖+((N:ℝ)+2))/2
    linarith
  have hmem : z ∈ Metric.eball (0:ℂ) (FormalMultilinearSeries.ofScalars ℂ (tailCoeff N)).radius := by
    apply lt_of_lt_of_le _ (tail_series_radius N r hr)
    change edist z 0 < (r:ℝ≥0∞)
    rw [edist_dist, dist_zero_right]
    exact (ENNReal.ofReal_lt_coe_iff (norm_nonneg z)).2 hzR
  exact (FormalMultilinearSeries.ofScalars ℂ (tailCoeff N)).analyticOnNhd z hmem

theorem tail_log_analytic (N : ℕ) (z : ℂ) (hz : ‖z‖ < (N:ℝ)+2) :
    AnalyticAt ℂ (tailLog N) z := by
  have h : tailLog N = fun w => w^4 * tailReduced N w := funext (tail_log_factor N)
  rw [h]
  exact (show AnalyticAt ℂ (fun w : ℂ => w^4) z by fun_prop).mul
    (tail_reduced_analytic N z hz)

theorem shell_analytic (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => regularizedShell w n) z := by
  unfold regularizedShell shellArgument
  fun_prop

theorem finite_head_analytic (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ n ∈ Finset.range N, regularizedShell w n) z := by
  induction N with
  | zero => simp; exact analyticAt_const
  | succ N ih =>
      simp only [Finset.prod_range_succ]
      exact ih.mul (shell_analytic N z)

theorem determinant_entire (z : ℂ) : AnalyticAt ℂ regularizedProduct z := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  have hz : ‖z‖ < (N:ℝ)+2 := by linarith
  have htail := tail_log_analytic N z hz
  have hexp : AnalyticAt ℂ Complex.exp (tailLog N z) := by fun_prop
  have ha := (finite_head_analytic N z).mul (hexp.comp htail)
  apply ha.congr
  have hopen : IsOpen {w : ℂ | ‖w‖ < (N:ℝ)+2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (product_factorization N w hw).symm

theorem determinant_analyticOnNhd_univ : AnalyticOnNhd ℂ regularizedProduct Set.univ :=
  fun z _ => determinant_entire z

end SharedCore.Det4Entire

#print axioms SharedCore.Det4Entire.tail_fourth_summable
#print axioms SharedCore.Det4Entire.tail_power_summable
#print axioms SharedCore.Det4Entire.tail_moment_nonneg
#print axioms SharedCore.Det4Entire.tail_fourth_nonneg
#print axioms SharedCore.Det4Entire.tail_power_bound
#print axioms SharedCore.Det4Entire.tail_moment_bound
#print axioms SharedCore.Det4Entire.tail_majorant_bound
#print axioms SharedCore.Det4Entire.tail_majorant_summable
#print axioms SharedCore.Det4Entire.tail_joint_norm_summable
#print axioms SharedCore.Det4Entire.tail_joint_summable
#print axioms SharedCore.Det4Entire.tail_joint_inner_moment
#print axioms SharedCore.Det4Entire.tail_argument_norm
#print axioms SharedCore.Det4Entire.tail_joint_inner_shell
#print axioms SharedCore.Det4Entire.tail_series_exchange
#print axioms SharedCore.Det4Entire.tail_log_hasSum
#print axioms SharedCore.Det4Entire.tail_exp_shell
#print axioms SharedCore.Det4Entire.tail_product_hasProd
#print axioms SharedCore.Det4Entire.full_product_hasProd
#print axioms SharedCore.Det4Entire.product_factorization
#print axioms SharedCore.Det4Entire.product_multipliable_everywhere
#print axioms SharedCore.Det4Entire.tail_coeff_norm
#print axioms SharedCore.Det4Entire.tail_series_radius
#print axioms SharedCore.Det4Entire.tail_log_factor
#print axioms SharedCore.Det4Entire.tail_reduced_analytic
#print axioms SharedCore.Det4Entire.tail_log_analytic
#print axioms SharedCore.Det4Entire.shell_analytic
#print axioms SharedCore.Det4Entire.finite_head_analytic
#print axioms SharedCore.Det4Entire.determinant_entire
#print axioms SharedCore.Det4Entire.determinant_analyticOnNhd_univ
