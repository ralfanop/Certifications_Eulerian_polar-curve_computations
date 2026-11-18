import Mathlib
import SharedCore.Det4ZetaMoments

/-! The complex logarithmic series and its actual regularized infinite
product for the diagonal fixture, on the open disk |z| < 2.
Uses the certified real moment majorant in Det4ZetaMoments. -/
namespace SharedCore.Det4Complex
open SharedCore.Det4Zeta

noncomputable def coefficient (z : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ)^(k+5) * z^(k+4) / ((k : ℂ)+4)

noncomputable def localLog (w : ℂ) : ℂ :=
  Complex.log (1+w) - w + w^2/2 - w^3/3

theorem local_log_hasSum (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (coefficient w) (localLog w) := by
  have h := (hasSum_nat_add_iff' 4).mpr (Complex.hasSum_taylorSeries_log hw)
  convert h using 1
  · funext k
    unfold coefficient
    push_cast
    rfl
  · unfold localLog
    norm_num [Finset.sum_range_succ] <;> ring

noncomputable def joint (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  coefficient z p.1 * (powerShell p.1 p.2 : ℂ)

private theorem shell_nonneg (k n : ℕ) : 0 ≤ powerShell k n := by
  unfold powerShell fourthShell
  positivity

theorem joint_norm (z : ℂ) (k n : ℕ) :
    ‖joint z (k,n)‖ = (‖z‖^(k+4) / ((k:ℝ)+4)) * powerShell k n := by
  have hcast : (k:ℂ)+4 = ((k+4:ℕ):ℂ) := by push_cast; rfl
  unfold joint coefficient
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, hcast, Complex.norm_natCast, Complex.norm_real, abs_of_nonneg (shell_nonneg k n)]
  push_cast
  rfl

private theorem joint_norm_inner (z : ℂ) (k : ℕ) :
    (∑' n : ℕ, ‖joint z (k,n)‖) = taylorMajorant ‖z‖ k := by
  simp_rw [joint_norm]
  rw [tsum_mul_left]
  unfold taylorMajorant powerMoment
  ring

theorem joint_norm_summable (z : ℂ) (hz : ‖z‖ < 2) :
    Summable (fun p : ℕ × ℕ => ‖joint z p‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (joint z p))).mpr
  constructor
  · intro k
    simp_rw [joint_norm]
    exact (power_shell_summable k).mul_left _
  · simp_rw [joint_norm_inner]
    exact taylor_majorant_summable ‖z‖ (norm_nonneg z) hz

theorem joint_summable (z : ℂ) (hz : ‖z‖ < 2) : Summable (joint z) :=
  (joint_norm_summable z hz).of_norm

theorem joint_inner_moment (z : ℂ) (k : ℕ) :
    (∑' n : ℕ, joint z (k,n)) = coefficient z k * (powerMoment k : ℂ) := by
  simp only [joint]
  rw [tsum_mul_left]
  unfold powerMoment
  rw [Complex.ofReal_tsum]

def multiplicity (n : ℕ) : ℕ := (n+1)*(n+2)
noncomputable def shellArgument (z : ℂ) (n : ℕ) : ℂ := z / ((n:ℂ)+2)

theorem shell_argument_norm_lt_one (z : ℂ) (hz : ‖z‖ < 2) (n : ℕ) :
    ‖shellArgument z n‖ < 1 := by
  have hcast : (n:ℂ)+2 = ((n+2:ℕ):ℂ) := by push_cast; rfl
  unfold shellArgument
  rw [norm_div, hcast, Complex.norm_natCast]
  apply (div_lt_one (by positivity)).2
  push_cast
  linarith [Nat.cast_nonneg (R := ℝ) n]

theorem joint_as_local (z : ℂ) (k n : ℕ) :
    joint z (k,n) = (multiplicity n : ℂ) * coefficient (shellArgument z n) k := by
  unfold joint coefficient powerShell fourthShell multiplicity shellArgument
  push_cast
  have hden : (n:ℂ)+2 ≠ 0 := by
    exact_mod_cast (show (n:ℝ)+2 ≠ 0 by positivity)
  have hk : (k:ℂ)+4 ≠ 0 := by
    exact_mod_cast (show (k:ℝ)+4 ≠ 0 by positivity)
  rw [div_pow, pow_add (a := (n:ℂ)+2)]
  field_simp <;> ring

noncomputable def shellLog (z : ℂ) (n : ℕ) : ℂ :=
  (multiplicity n : ℂ) * localLog (shellArgument z n)

theorem joint_inner_shell (z : ℂ) (hz : ‖z‖ < 2) (n : ℕ) :
    (∑' k : ℕ, joint z (k,n)) = shellLog z n := by
  simp_rw [joint_as_local]
  rw [tsum_mul_left]
  unfold shellLog
  rw [(local_log_hasSum _ (shell_argument_norm_lt_one z hz n)).tsum_eq]

noncomputable def globalLog (z : ℂ) : ℂ :=
  ∑' k : ℕ, coefficient z k * (powerMoment k : ℂ)

theorem global_series_exchange (z : ℂ) (hz : ‖z‖ < 2) :
    (∑' n : ℕ, shellLog z n) = globalLog z := by
  unfold globalLog
  simp_rw [← joint_inner_shell z hz]
  simp_rw [← joint_inner_moment z]
  exact (joint_summable z hz).tsum_comm

theorem shell_log_hasSum (z : ℂ) (hz : ‖z‖ < 2) :
    HasSum (shellLog z) (globalLog z) := by
  have h := (joint_summable z hz).prod_symm.prod
  have hs : Summable (shellLog z) := by
    convert h using 1
    funext n
    exact (joint_inner_shell z hz n).symm
  rw [← global_series_exchange z hz]
  exact hs.hasSum

theorem global_log_summable (z : ℂ) (hz : ‖z‖ < 2) :
    Summable (fun k : ℕ => coefficient z k * (powerMoment k : ℂ)) := by
  have h := (joint_summable z hz).prod
  convert h using 1
  funext k
  exact (joint_inner_moment z k).symm

noncomputable def regularizedShell (z : ℂ) (n : ℕ) : ℂ :=
  let w := shellArgument z n
  ((1+w) * Complex.exp (-w+w^2/2-w^3/3)) ^ multiplicity n

theorem exp_regularized_shell (z : ℂ) (hz : ‖z‖ < 2) (n : ℕ) :
    Complex.exp (shellLog z n) = regularizedShell z n := by
  have hnorm := shell_argument_norm_lt_one z hz n
  have hne : 1 + shellArgument z n ≠ 0 := by
    intro h
    have he : shellArgument z n = -1 := by linear_combination h
    rw [he] at hnorm
    norm_num at hnorm
  unfold shellLog regularizedShell localLog
  rw [Complex.exp_nat_mul]
  congr 1
  rw [show Complex.log (1+shellArgument z n) - shellArgument z n +
        shellArgument z n^2/2 - shellArgument z n^3/3 =
       Complex.log (1+shellArgument z n) +
        (-shellArgument z n+shellArgument z n^2/2-shellArgument z n^3/3) by ring,
      Complex.exp_add, Complex.exp_log hne]

noncomputable def regularizedProduct (z : ℂ) : ℂ :=
  ∏' n : ℕ, regularizedShell z n

theorem regularized_product_hasProd (z : ℂ) (hz : ‖z‖ < 2) :
    HasProd (regularizedShell z) (Complex.exp (globalLog z)) := by
  have h := (shell_log_hasSum z hz).cexp
  convert h using 1
  funext n
  exact (exp_regularized_shell z hz n).symm

theorem regularized_product_eq_exp (z : ℂ) (hz : ‖z‖ < 2) :
    regularizedProduct z = Complex.exp (globalLog z) :=
  (regularized_product_hasProd z hz).tprod_eq

theorem regularized_product_ne_zero (z : ℂ) (hz : ‖z‖ < 2) :
    regularizedProduct z ≠ 0 := by
  rw [regularized_product_eq_exp z hz]
  exact Complex.exp_ne_zero _

theorem fourth_coefficient :
    ((-1 : ℂ)^5 / 4) * (powerMoment 0 : ℂ) =
      -(riemannZeta 2 - riemannZeta 3) / 4 := by
  rw [power_moment_identification, zero_add, moment_riemannZeta_difference 4 (by norm_num)]
  norm_num <;> ring

end SharedCore.Det4Complex

#print axioms SharedCore.Det4Complex.local_log_hasSum
#print axioms SharedCore.Det4Complex.joint_norm
#print axioms SharedCore.Det4Complex.joint_norm_summable
#print axioms SharedCore.Det4Complex.joint_summable
#print axioms SharedCore.Det4Complex.joint_inner_moment
#print axioms SharedCore.Det4Complex.shell_argument_norm_lt_one
#print axioms SharedCore.Det4Complex.joint_as_local
#print axioms SharedCore.Det4Complex.joint_inner_shell
#print axioms SharedCore.Det4Complex.global_series_exchange
#print axioms SharedCore.Det4Complex.shell_log_hasSum
#print axioms SharedCore.Det4Complex.global_log_summable
#print axioms SharedCore.Det4Complex.exp_regularized_shell
#print axioms SharedCore.Det4Complex.regularized_product_hasProd
#print axioms SharedCore.Det4Complex.regularized_product_eq_exp
#print axioms SharedCore.Det4Complex.regularized_product_ne_zero
#print axioms SharedCore.Det4Complex.fourth_coefficient
