import SpecialImaginaryPoint.EulerianSpinCatalanRemainder
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! M14: identification of all coefficients with the actual Catalan sequence.
The continuous angular density is the nonsingular parametrization of the
Beta(1/2,3/2) moments. The geometric remainder identity is pointwise. -/
namespace M14.EulerianSpin
open scoped BigOperators
open Finset
noncomputable section

def catMoment (n : ℕ) : ℝ := (catalan n : ℝ)/4^n

theorem catMoment_zero : catMoment 0 = 1 := by
  simp [catMoment,catalan_zero]

theorem catMoment_recurrence (n : ℕ) :
    ((n:ℝ)+2)*catMoment (n+1) = ((n:ℝ)+1/2)*catMoment n := by
  have h1 : ((n:ℝ)+1)*(catalan n:ℝ) = (Nat.centralBinom n:ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have h2 : ((n:ℝ)+2)*(catalan (n+1):ℝ) = (Nat.centralBinom (n+1):ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (n+1)
  have h3 : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ) =
      2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  rw [← h1,← h2] at h3
  have h4 : ((n:ℝ)+2)*(catalan (n+1):ℝ) =
      2*(2*(n:ℝ)+1)*(catalan n:ℝ) := by
    apply mul_left_cancel₀ (show (n:ℝ)+1 ≠ 0 by positivity)
    linear_combination h3
  unfold catMoment
  rw [pow_succ]
  field_simp
  linear_combination h4

theorem halfFalling_catalan (n : ℕ) :
    2*halfFalling (n+1)/(Nat.factorial (n+1):ℝ) =
      (-1:ℝ)^n*catMoment n := by
  induction n with
  | zero => norm_num [halfFalling,catMoment,catalan_zero,Nat.factorial]
  | succ n ih =>
    have hn : (Nat.factorial (n+1):ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n+1)
    have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
    have hc := catMoment_recurrence n
    have he : 2*halfFalling (n+1+1)/(Nat.factorial (n+1+1):ℝ) =
        (2*halfFalling (n+1)/(Nat.factorial (n+1):ℝ)) *
          (-(n:ℝ)-1/2)/((n:ℝ)+2) := by
      rw [halfFalling,Nat.factorial_succ]
      push_cast
      field_simp [hn,hn2]
      <;> ring
    rw [he,ih,pow_succ]
    field_simp [hn2]
    linear_combination -(-1:ℝ)^n * hc

theorem catMoment_nonneg (n : ℕ) : 0 ≤ catMoment n := by
  unfold catMoment
  positivity

theorem halfFalling_abs_catalan (n : ℕ) :
    2*|halfFalling (n+1)/(Nat.factorial (n+1):ℝ)| = catMoment n := by
  have h := congrArg abs (halfFalling_catalan n)
  change |2*halfFalling (n+1)/(Nat.factorial (n+1):ℝ)| = |(-1:ℝ)^n*catMoment n| at h
  rw [mul_div_assoc,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_nonneg (catMoment_nonneg n)] at h
  convert h using 1 <;> ring

def catalanSpinTaylor (j : ℝ) (N : ℕ) : ℝ :=
  4*j+2+∑ k ∈ Finset.range (N+1), (-1:ℝ)^k*catMoment k/j^k

theorem spinTaylor_catalan (j : ℝ) (hj : 0 < j) (N : ℕ) :
    spinTaylor j N = catalanSpinTaylor j N := by
  induction N with
  | zero =>
    unfold spinTaylor halfTaylor catalanSpinTaylor
    norm_num [Finset.sum_range_succ,halfFalling,catMoment,catalan_zero,Nat.factorial]
    field_simp [hj.ne'] <;> ring
  | succ N ih =>
    have h := halfFalling_catalan (N+1)
    have ht : spinTaylor j (N+1) =
      spinTaylor j N + (2*halfFalling (N+2)/(Nat.factorial (N+2):ℝ))/j^(N+1) := by
      unfold spinTaylor halfTaylor
      rw [Finset.sum_range_succ]
      rw [div_pow,one_pow,show j^(N+2)=j^(N+1)*j by rw [← pow_succ]]
      field_simp [hj.ne'] <;> ring
    rw [ht,ih,h]
    unfold catalanSpinTaylor
    rw [Finset.sum_range_succ]
    ring

theorem spin_catalan_total_error (j : ℝ) (hj : (1:ℝ)/2 ≤ j) (N : ℕ) :
    |spinCritical j-catalanSpinTaylor j N| <
      catMoment (N+1)/j^(N+1) +
      spinReference j^2/(Real.exp (spinReference j-1)-1) := by
  have h := spin_total_error j hj N
  rw [spinTaylor_catalan j (by linarith) N,halfFalling_abs_catalan (N+1)] at h
  exact h

/-- Finite geometric identity, no convergence hypothesis on s*x. -/
theorem geometric_resolvent_split (s x : ℝ) (h : 1+s*x ≠ 0) (N : ℕ) :
    1/(1+s*x) =
      (∑ k ∈ Finset.range (N+1), (-s*x)^k) +
      (-s*x)^(N+1)/(1+s*x) := by
  induction N with
  | zero =>
    simp
    field_simp [h] <;> ring
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range (N+1), (-s*x)^k) +
          (-s*x)^(N+1)/(1+s*x) := ih
      _ = _ := by rw [pow_succ (-s*x) (N+1)]; field_simp [h] <;> ring

/-- Angular version of the beta moment, with smooth density on [0,pi]. -/
def angularMoment (n : ℕ) : ℝ :=
  (2/Real.pi) * ∫ t in (0:ℝ)..Real.pi, Real.sin t^(2*n)*Real.cos t^2

def sinEven (n : ℕ) : ℝ := ∫ t in (0:ℝ)..Real.pi, Real.sin t^(2*n)

theorem sinEven_recurrence (n : ℕ) :
    sinEven (n+1) = (2*(n:ℝ)+1)/(2*(n:ℝ)+2)*sinEven n := by
  unfold sinEven
  rw [show 2*(n+1)=2*n+2 by omega,integral_sin_pow]
  simp [Real.sin_pi,Real.sin_zero]
  push_cast
  <;> ring

theorem sinEven_central (n : ℕ) :
    sinEven n = Real.pi*(Nat.centralBinom n:ℝ)/4^n := by
  induction n with
  | zero => simp [sinEven,Nat.centralBinom_zero]
  | succ n ih =>
    rw [sinEven_recurrence,ih,pow_succ]
    have h : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ) =
      2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    field_simp
    linear_combination -Real.pi*h

theorem angularMoment_eq (n : ℕ) : angularMoment n = catMoment n := by
  have h : (∫ t in (0:ℝ)..Real.pi, Real.sin t^(2*n)*Real.cos t^2) =
      sinEven n - sinEven (n+1) := by
    unfold sinEven
    rw [← intervalIntegral.integral_sub ((Real.continuous_sin.pow (2*n)).intervalIntegrable _ _) ((Real.continuous_sin.pow (2*(n+1))).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    rw [show 2*(n+1)=2*n+2 by omega,pow_add]
    have he := Real.sin_sq_add_cos_sq t
    linear_combination Real.sin t^(2*n)*he
  rw [angularMoment,h,sinEven_recurrence,sinEven_central]
  have hc : ((n:ℝ)+1)*(catalan n:ℝ) = (Nat.centralBinom n:ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  rw [← hc]
  unfold catMoment
  field_simp [Real.pi_ne_zero]
  <;> ring

#print axioms catMoment_zero
#print axioms catMoment_recurrence
#print axioms halfFalling_catalan
#print axioms catMoment_nonneg
#print axioms halfFalling_abs_catalan
#print axioms spinTaylor_catalan
#print axioms spin_catalan_total_error
#print axioms geometric_resolvent_split
#print axioms sinEven_recurrence
#print axioms sinEven_central
#print axioms angularMoment_eq

end
end M14.EulerianSpin
