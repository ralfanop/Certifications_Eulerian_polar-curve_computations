import EulerianGrothendieck.UniformVacuumAsymptotics
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Central

/-! Exact analytic sum of the central-binomial series, derived from a formal
series differential equation and a justified Cauchy product. -/
noncomputable section
open scoped BigOperators
open Finset PowerSeries
namespace EulerianGrothendieck

def centralCoefficient (k : ℕ) : ℝ := (k.centralBinom:ℝ)/4^k

def centralSeries : PowerSeries ℝ := PowerSeries.mk centralCoefficient

@[simp] theorem centralCoefficient_zero : centralCoefficient 0 = 1 := by
  simp [centralCoefficient]

theorem centralCoefficient_nonneg (k : ℕ) : 0 ≤ centralCoefficient k := by
  unfold centralCoefficient
  positivity

theorem centralCoefficient_le_one (k : ℕ) : centralCoefficient k ≤ 1 := by
  have h := binomialWeight_le_geometric 1 k
  simpa [binomialWeight, centralCoefficient, Nat.centralBinom] using h

theorem centralCoefficient_recurrence (k : ℕ) :
    (k+1:ℝ)*centralCoefficient (k+1) = (k+1/2:ℝ)*centralCoefficient k := by
  have h : (k+1:ℝ)*((k+1).centralBinom:ℝ) = 2*(2*(k:ℝ)+1)*(k.centralBinom:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold centralCoefficient
  rw [pow_succ]
  field_simp
  nlinarith

@[simp] theorem centralSeries_coeff (k : ℕ) : PowerSeries.coeff k centralSeries = centralCoefficient k :=
  PowerSeries.coeff_mk _ _

theorem centralSeries_ode :
    (1-PowerSeries.X)*PowerSeries.derivative ℝ centralSeries = PowerSeries.C (1/2:ℝ)*centralSeries := by
  ext n
  cases n with
  | zero =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
    norm_num [centralSeries_coeff, centralCoefficient, Nat.centralBinom]
  | succ n =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
      centralSeries_coeff, centralSeries_coeff]
    have h := centralCoefficient_recurrence (n+1)
    push_cast at h ⊢
    linarith

theorem centralSeries_square_ode :
    (1-PowerSeries.X)*PowerSeries.derivative ℝ (centralSeries^2) = centralSeries^2 := by
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  have h := congrArg (fun q : PowerSeries ℝ => (2*centralSeries)*q) centralSeries_ode
  have hc : (2:PowerSeries ℝ)*PowerSeries.C (1/2:ℝ) = 1 := by
    calc
      _ = PowerSeries.C (1/2:ℝ) + PowerSeries.C (1/2:ℝ) := by ring
      _ = PowerSeries.C ((1/2:ℝ)+1/2) := (map_add _ _ _).symm
      _ = 1 := by norm_num
  calc
    _ = (2*centralSeries)*((1-PowerSeries.X)*PowerSeries.derivative ℝ centralSeries) := by norm_num; ring
    _ = (2*centralSeries)*(PowerSeries.C (1/2:ℝ)*centralSeries) := h
    _ = ((2:PowerSeries ℝ)*PowerSeries.C (1/2:ℝ))*centralSeries^2 := by ring
    _ = centralSeries^2 := by rw [hc, one_mul]

theorem centralSeries_square_coeff (n : ℕ) : PowerSeries.coeff n (centralSeries^2) = 1 := by
  induction n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp [centralSeries, PowerSeries.constantCoeff_mk]
  | succ n ih =>
    have h := congrArg (PowerSeries.coeff (R := ℝ) n) centralSeries_square_ode
    cases n with
    | zero =>
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative, ih] at h
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X,
        zero_mul, sub_zero, Nat.cast_zero, zero_add, mul_one] using h
    | succ n =>
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, ih] at h
      have hn : (n+2:ℝ) ≠ 0 := by positivity
      push_cast at h
      apply (mul_right_cancel₀ hn)
      nlinarith

theorem centralCoefficient_self_convolution (n : ℕ) :
    (∑ j ∈ range (n+1), centralCoefficient j*centralCoefficient (n-j)) = 1 := by
  have h := centralSeries_square_coeff n
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j l => PowerSeries.coeff j centralSeries*PowerSeries.coeff l centralSeries) n] at h
  simpa only [centralSeries_coeff] using h

theorem centralCoefficient_geometric_summable (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun k => centralCoefficient k*s^k) := by
  apply (hasSum_geometric_of_lt_one hs0 hs1).summable.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (centralCoefficient_nonneg k) (pow_nonneg hs0 _))]
  exact mul_le_of_le_one_left (pow_nonneg hs0 _) (centralCoefficient_le_one k)

theorem centralBinomial_sum_square (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑' k, centralCoefficient k*s^k)^2 = 1/(1-s) := by
  have hs := centralCoefficient_geometric_summable s hs0 hs1
  have hnorm := summable_norm_iff.mpr hs
  have hp := hasSum_sum_range_mul_of_summable_norm hnorm hnorm
  have heq : ∀ n : ℕ, (∑ j ∈ range (n+1),
      (centralCoefficient j*s^j)*(centralCoefficient (n-j)*s^(n-j))) = s^n := by
    intro n
    calc
      _ = (∑ j ∈ range (n+1), centralCoefficient j*centralCoefficient (n-j))*s^n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (centralCoefficient j*s^j)*(centralCoefficient (n-j)*s^(n-j)) =
          (centralCoefficient j*centralCoefficient (n-j))*(s^j*s^(n-j)) by ring,
          ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      _ = s^n := by rw [centralCoefficient_self_convolution, one_mul]
  simp_rw [heq] at hp
  have h := hp.unique (hasSum_geometric_of_lt_one hs0 hs1)
  simpa only [pow_two, one_div] using h

theorem centralBinomial_sum (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑' k, centralCoefficient k*s^k) = 1/Real.sqrt (1-s) := by
  have h0 : 0 ≤ ∑' k, centralCoefficient k*s^k :=
    tsum_nonneg (fun k => mul_nonneg (centralCoefficient_nonneg k) (pow_nonneg hs0 _))
  have hsq := centralBinomial_sum_square s hs0 hs1
  have hsqrt : 0 < Real.sqrt (1-s) := Real.sqrt_pos.2 (by linarith)
  have hsq' : (1/Real.sqrt (1-s))^2 = 1/(1-s) := by
    rw [div_pow, Real.sq_sqrt (by linarith)]; norm_num
  nlinarith [show 0 ≤ 1/Real.sqrt (1-s) by positivity]

theorem uniformNormCoefficient_zero_closed (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    uniformNormCoefficient t 0 = 1/Real.sqrt (1-t^2) := by
  rw [uniformNormCoefficient_zero]
  have he : ∀ k, binomialWeight t k = centralCoefficient k*(t^2)^k := by
    intro k
    simp [binomialWeight, centralCoefficient, Nat.centralBinom, pow_mul]
  simp_rw [he]
  exact centralBinomial_sum (t^2) (sq_nonneg t) (by nlinarith)

end EulerianGrothendieck
