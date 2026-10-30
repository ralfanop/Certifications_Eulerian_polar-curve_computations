import EulerianGrothendieck.CoefficientIdentification

noncomputable section
open scoped BigOperators
open Finset
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

def centralFactorialMoment (s : ℝ) (q : ℕ) : ℝ :=
  ∑' k : ℕ, fallingReal q k * centralCoefficient k * s^k

theorem centralFactorialMoment_summable (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (q : ℕ) :
    Summable (fun k : ℕ => fallingReal q k * centralCoefficient k * s^k) := by
  apply (shifted_power_geometric_summable s hs0 hs1 q).of_norm_bounded
  intro k
  have hc0 := centralCoefficient_nonneg k
  rw [fallingReal_nat, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hd : (k.descFactorial q:ℝ) ≤ (k:ℝ)^q := by exact_mod_cast Nat.descFactorial_le_pow k q
  have hc := centralCoefficient_le_one k
  have hk : (k:ℝ)^q ≤ (k+1:ℝ)^q := pow_le_pow_left₀ (by positivity) (by linarith) q
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (mul_le_of_le_one_right (by positivity) hc).trans (hd.trans hk)

theorem centralFactorialMoment_recurrence (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (q : ℕ) :
    (1-s)*centralFactorialMoment s (q+1) = s*(q+1/2:ℝ)*centralFactorialMoment s q := by
  let f := fun (j k : ℕ) => fallingReal j k * centralCoefficient k * s^k
  have hsum := centralFactorialMoment_summable s hs0 hs1 (q+1)
  change Summable (f (q+1)) at hsum
  have hz : f (q+1) 0 = 0 := by simp [f, fallingReal_nat, Nat.zero_descFactorial_succ]
  have hshift : ∀ k, f (q+1) (k+1) = s*(f (q+1) k + (q+1/2:ℝ)*f q k) := by
    intro k
    have hd : fallingReal (q+1) (k+1:ℝ) = (k+1:ℝ)*fallingReal q k := by
      calc
        _ = ((k+1).descFactorial (q+1):ℝ) := by simpa using fallingReal_nat (q+1) (k+1)
        _ = _ := by rw [Nat.succ_descFactorial_succ, Nat.cast_mul, fallingReal_nat]; push_cast; rfl
    dsimp [f]
    push_cast
    rw [hd, fallingReal, pow_succ]
    calc
      _ = fallingReal q k * ((k+1:ℝ)*centralCoefficient (k+1)) * s^k * s := by ring
      _ = _ := by rw [centralCoefficient_recurrence]; ring
  have hs : centralFactorialMoment s (q+1) =
      s*(centralFactorialMoment s (q+1)+(q+1/2:ℝ)*centralFactorialMoment s q) := by
    change (∑' k, f (q+1) k) = _
    rw [hsum.tsum_eq_zero_add, hz, zero_add]
    simp_rw [hshift]
    rw [tsum_mul_left, hsum.tsum_add ((centralFactorialMoment_summable s hs0 hs1 q).mul_left (q+1/2:ℝ)),
      tsum_mul_left]
    rfl
  linarith

theorem centralFactorialMoment_zero (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    centralFactorialMoment s 0 = 1/Real.sqrt (1-s) := by
  simpa [centralFactorialMoment, fallingReal] using centralBinomial_sum s hs0.le hs1

theorem nbFactorial_recurrence_real (q : ℕ) :
    (nbFactorial (q+1):ℝ) = ((q+1/2:ℝ)/4)*(nbFactorial q:ℝ) := by
  unfold nbFactorial
  push_cast
  rw [show 2*(q+1)=2*q+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem centralFactorialMoment_one_fifth (q : ℕ) :
    centralFactorialMoment (1/5) q = (1/Real.sqrt (4/5))*(nbFactorial q:ℝ) := by
  induction q with
  | zero => norm_num [centralFactorialMoment_zero (1/5) (by norm_num) (by norm_num), nbFactorial]
  | succ q ih =>
    have h := centralFactorialMoment_recurrence (1/5) (by norm_num) (by norm_num) q
    rw [ih] at h
    rw [nbFactorial_recurrence_real]
    nlinarith [h]

end EulerianGrothendieck
