import SpecialImaginaryPoint.EulerianSpinSharpAsymptotics
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Explicit algebraic plus exponential remainder for the actual Langevin inverse.
The recursive falling factorial represents the Taylor coefficients of the square root.
All estimates are for the actual spinCritical, not a surrogate. -/
namespace M14.EulerianSpin
open M14.EulerianLegendre
open Filter Set Finset
open scoped Topology BigOperators
noncomputable section

theorem spinReference_gt_four (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    4 < spinReference j := by
  have hp : 0 ≤ j*(j+1) := by positivity
  have hs := Real.sq_sqrt hp
  have hq : (3:ℝ)/4 ≤ j*(j+1) := by
    nlinarith [mul_nonneg (show 0 ≤ j-1/2 by linarith) (show 0 ≤ j+3/2 by linarith)]
  have hroot : (1:ℝ)/2 < Real.sqrt (j*(j+1)) := by
    by_contra! h
    nlinarith [Real.sqrt_nonneg (j*(j+1)), mul_nonneg (Real.sqrt_nonneg (j*(j+1))) (show 0 ≤ 1/2-Real.sqrt (j*(j+1)) by linarith)]
  unfold spinReference
  linarith

theorem exp_gt_quadratic (x : ℝ) (hx : 3 < x) :
    x*(x+1) < Real.exp x-1 := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ x by linarith) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hm : 0 < x^2*(x-3) := mul_pos (by positivity) (by linarith)
  nlinarith only [he,hm]

theorem spinCritical_gt_reference_sub_one (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    spinReference j-1 < spinCritical j := by
  have hjp : 0 < j := by linarith
  let R := spinReference j
  let x := R-1
  have hR : 4 < R := spinReference_gt_four j hj
  have hx : 3 < x := by dsimp [x]; linarith
  have hxpos : 0 < x := by linarith
  have hRp : 0 < R := by linarith
  have heta := spinRatio_gt_one j hjp
  have hg : 0 < 1-1/spinRatio j := by
    have h := (div_lt_iff₀ (show 0 < spinRatio j by linarith)).2 heta
    linarith
  have href := reference_spin_eq j hjp
  change 2/(1-1/spinRatio j) = R at href
  have hprod := (div_eq_iff hg.ne').1 href
  have htarget : 1/spinRatio j = 1-2/R := by
    have h : 2/R = 1-1/spinRatio j := (div_eq_iff hRp.ne').2 (by nlinarith only [hprod])
    linarith only [h]
  have hex : R*x < Real.exp x-1 := by
    have h := exp_gt_quadratic x hx
    have hRx : R = x+1 := by dsimp [x]; ring
    calc
      R*x = x*(x+1) := by rw [hRx]; ring
      _ < _ := h
  have hdiv : 2/(Real.exp x-1) < 2/(R*x) :=
    div_lt_div_of_pos_left (by norm_num) (mul_pos hRp hxpos) hex
  have hdiff : 2/x-2/R = 2/(R*x) := by
    field_simp [hxpos.ne',hRp.ne']
    dsimp [x]
    <;> ring
  have hL : langevin (x/2) < langevin (spinCritical j/2) := by
    change langevin (x/2) < langevin (critical (spinRatio j)/2)
    rw [critical_exact _ heta,langevin_exp_form _ (by linarith : 0 < x/2),
      show 2*(x/2)=x by ring,show 1/(x/2)=2/x by ring,htarget]
    linarith only [hdiv,hdiff]
  have h := langevin_strictMono.lt_iff_lt.mp hL
  change x < spinCritical j
  linarith

theorem spin_exponential_error (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    0 < spinReference j-spinCritical j ∧
    spinReference j-spinCritical j <
      spinReference j^2/(Real.exp (spinReference j-1)-1) := by
  have hjp : 0 < j := by linarith
  have hlt := threshold_lt_reference (spinRatio j) (spinRatio_gt_one j hjp)
  rw [reference_spin_eq j hjp] at hlt
  change spinCritical j < spinReference j at hlt
  have hc := threshold_correction (spinRatio j) (spinRatio_gt_one j hjp)
  rw [reference_spin_eq j hjp] at hc
  change spinReference j-spinCritical j =
    spinReference j*spinCritical j/(Real.exp (spinCritical j)-1) at hc
  have hr := spinReference_gt_four j hj
  have hlo := spinCritical_gt_reference_sub_one j hj
  have hden : 0 < Real.exp (spinReference j-1)-1 := by
    have h := Real.exp_lt_exp.mpr (show (0:ℝ) < spinReference j-1 by linarith)
    rw [Real.exp_zero] at h
    exact sub_pos.mpr h
  have hd : Real.exp (spinReference j-1)-1 < Real.exp (spinCritical j)-1 :=
    sub_lt_sub_right (Real.exp_lt_exp.mpr hlo) 1
  constructor
  · linarith
  · rw [hc]
    calc
      _ < spinReference j*spinReference j/(Real.exp (spinCritical j)-1) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt (by linarith)) (hden.trans hd)
      _ ≤ spinReference j^2/(Real.exp (spinReference j-1)-1) := by
        rw [pow_two]
        exact div_le_div_of_nonneg_left (by positivity) hden hd.le

/-- Falling product (1/2)(1/2-1)...(1/2-n+1). -/
def halfFalling : ℕ → ℝ
  | 0 => 1
  | n+1 => halfFalling n * (1/2-(n:ℝ))

def halfTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), halfFalling k / (k.factorial:ℝ) * x^k

theorem half_iteratedDeriv (n : ℕ) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n (fun u : ℝ => u ^ (1/2:ℝ)) t =
      halfFalling n * t ^ ((1/2:ℝ)-(n:ℝ)) := by
  induction n generalizing t with
  | zero => simp [halfFalling]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun u : ℝ => u ^ (1/2:ℝ)) =ᶠ[𝓝 t]
        (fun u : ℝ => halfFalling n * u ^ ((1/2:ℝ)-(n:ℝ))) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ih u hu
    rw [he.deriv_eq]
    rw [((Real.hasDerivAt_rpow_const (p := (1/2:ℝ)-(n:ℝ))
        (Or.inl ht.ne')).const_mul (halfFalling n)).deriv]
    rw [halfFalling, Nat.cast_succ,show (1/2:ℝ)-((n:ℝ)+1) = 1/2-(n:ℝ)-1 by ring]
    ring

/-- Actual Lagrange remainder: no assumed Taylor estimate. -/
theorem halfTaylor_lagrange (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ t ∈ Set.Ioo (1:ℝ) (1+x),
      (1+x) ^ (1/2:ℝ)-halfTaylor n x =
        (halfFalling (n+1)/(Nat.factorial (n+1):ℝ)) *
        x^(n+1) * t ^ ((1/2:ℝ)-((n+1:ℕ):ℝ)) := by
  let f : ℝ → ℝ := fun u => u ^ (1/2:ℝ)
  have hab : (1:ℝ) < 1+x := by linarith
  have hcd : ContDiffOn ℝ (n+1) f (Set.Icc 1 (1+x)) := by
    intro t ht
    exact (Real.contDiffAt_rpow_const_of_ne (p := (1/2:ℝ))
      (show t ≠ 0 by have := ht.1; linarith)).contDiffWithinAt
  obtain ⟨t,ht,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hab hcd
  have hte : taylorWithinEval f n (Set.Icc 1 (1+x)) 1 (1+x) = halfTaylor n x := by
    rw [taylor_within_apply]
    unfold halfTaylor
    apply Finset.sum_congr rfl
    intro k hk
    have hc : ContDiffAt ℝ k f 1 := Real.contDiffAt_rpow_const_of_ne (by norm_num)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hc ⟨le_rfl,hab.le⟩]
    rw [show iteratedDeriv k f 1 = halfFalling k * (1:ℝ)^((1/2:ℝ)-(k:ℝ)) from
      half_iteratedDeriv k 1 (by norm_num)]
    simp only [Real.one_rpow,mul_one,smul_eq_mul,show (1+x)-1=x by ring]
    ring
  refine ⟨t,ht,?_⟩
  rw [hte] at h
  change (1+x) ^ (1/2:ℝ)-halfTaylor n x = _ at h
  rw [show iteratedDeriv (n+1) f t = _ from half_iteratedDeriv (n+1) t (by have := ht.1; linarith)] at h
  rw [show (1+x)-1=x by ring] at h
  convert h using 1 <;> ring

theorem halfTaylor_error (n : ℕ) (x : ℝ) (hx : 0 < x) :
    |(1+x) ^ (1/2:ℝ)-halfTaylor n x| ≤
      |halfFalling (n+1)/(Nat.factorial (n+1):ℝ)| * x^(n+1) := by
  obtain ⟨t,ht,h⟩ := halfTaylor_lagrange n x hx
  have hp : 0 < t := by have := ht.1; linarith
  have he : (1/2:ℝ)-((n+1:ℕ):ℝ) ≤ 0 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos ht.1.le he
  rw [h,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hx.le _),
    abs_of_nonneg (Real.rpow_nonneg hp.le _)]
  exact mul_le_of_le_one_right (by positivity) hpow

def spinTaylor (j : ℝ) (N : ℕ) : ℝ :=
    2*(j+1+j*halfTaylor (N+1) (1/j))

theorem spinReference_rpow (j : ℝ) (hj : 0 < j) :
    spinReference j = 2*(j+1+j*(1+1/j) ^ (1/2:ℝ)) := by
  unfold spinReference
  rw [show j*(j+1)=j^2*(1+1/j) by field_simp [hj.ne'] <;> ring,
    Real.sqrt_mul (sq_nonneg j), Real.sqrt_sq_eq_abs,abs_of_pos hj,Real.sqrt_eq_rpow]

theorem spin_algebraic_error (j : ℝ) (hj : 0 < j) (N : ℕ) :
    |spinReference j-spinTaylor j N| ≤
      2*|halfFalling (N+2)/(Nat.factorial (N+2):ℝ)|/j^(N+1) := by
  have h := halfTaylor_error (N+1) (1/j) (by positivity)
  rw [spinReference_rpow j hj,spinTaylor,
    show 2*(j+1+j*(1+1/j) ^ (1/2:ℝ))-2*(j+1+j*halfTaylor (N+1) (1/j)) =
      (2*j)*((1+1/j) ^ (1/2:ℝ)-halfTaylor (N+1) (1/j)) by ring,
    abs_mul,abs_of_pos (by positivity : 0 < 2*j)]
  calc
    _ ≤ (2*j)*(|halfFalling (N+2)/(Nat.factorial (N+2):ℝ)|*(1/j)^(N+2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [div_pow,one_pow,show j^(N+2)=j^(N+1)*j by rw [← pow_succ]; congr 1 <;> omega]
      field_simp [hj.ne'] <;> ring

theorem spin_total_error (j : ℝ) (hj : (1:ℝ)/2 ≤ j) (N : ℕ) :
    |spinCritical j-spinTaylor j N| <
      2*|halfFalling (N+2)/(Nat.factorial (N+2):ℝ)|/j^(N+1) +
      spinReference j^2/(Real.exp (spinReference j-1)-1) := by
  have h := spin_exponential_error j hj
  have ha := spin_algebraic_error j (by linarith) N
  calc
    _ = |(spinCritical j-spinReference j)+(spinReference j-spinTaylor j N)| := by ring_nf
    _ ≤ |spinCritical j-spinReference j|+|spinReference j-spinTaylor j N| := abs_add_le _ _
    _ < _ := by rw [abs_sub_comm (spinCritical j),abs_of_pos h.1]; linarith only [h.2,ha]

theorem halfFalling_22_coefficient :
    2*|halfFalling 22/(Nat.factorial 22:ℝ)| = (24466267020:ℝ)/4^21 := by
  norm_num [halfFalling, Nat.factorial, abs_of_nonpos, abs_of_nonneg]

theorem spin_order20_error (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    |spinCritical j-spinTaylor j 20| <
      (24466267020:ℝ)/(4^21*j^21) +
      spinReference j^2/(Real.exp (spinReference j-1)-1) := by
  have h := spin_total_error j hj 20
  change |spinCritical j-spinTaylor j 20| <
    2*|halfFalling 22/(Nat.factorial 22:ℝ)|/j^21 +
      spinReference j^2/(Real.exp (spinReference j-1)-1) at h
  rw [halfFalling_22_coefficient,div_div] at h
  exact h

theorem spin_order20_upper (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    spinCritical j < spinTaylor j 20 := by
  have hjp : 0 < j := by linarith
  obtain ⟨t,ht,h⟩ := halfTaylor_lagrange 21 (1/j) (by positivity)
  have hc : halfFalling 22/(Nat.factorial 22:ℝ) < 0 := by
    norm_num [halfFalling, Nat.factorial]
  have htpos : 0 < t := by have := ht.1; linarith
  have hneg : (1+1/j) ^ (1/2:ℝ)-halfTaylor 21 (1/j) < 0 := by
    rw [h]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (by positivity)) (Real.rpow_pos_of_pos htpos _)
  have hpoly : spinReference j < spinTaylor j 20 := by
    rw [spinReference_rpow j hjp,spinTaylor]
    have hmul := mul_lt_mul_of_pos_left (sub_neg.mp hneg) hjp
    linarith only [hmul]
  exact (sub_pos.mp (spin_exponential_error j hj).1).trans hpoly

theorem spin_order20_signed_error (j : ℝ) (hj : (1:ℝ)/2 ≤ j) :
    0 < spinTaylor j 20-spinCritical j ∧
    spinTaylor j 20-spinCritical j <
      (24466267020:ℝ)/(4^21*j^21) +
      spinReference j^2/(Real.exp (spinReference j-1)-1) := by
  have hp := sub_pos.mpr (spin_order20_upper j hj)
  have h := spin_order20_error j hj
  rw [abs_sub_comm,abs_of_pos hp] at h
  exact ⟨hp,h⟩

#print axioms spin_order20_upper
#print axioms spin_order20_signed_error
#print axioms spinReference_gt_four
#print axioms exp_gt_quadratic
#print axioms spinCritical_gt_reference_sub_one
#print axioms spin_exponential_error
#print axioms half_iteratedDeriv
#print axioms halfTaylor_lagrange
#print axioms halfTaylor_error
#print axioms spinReference_rpow
#print axioms spin_algebraic_error
#print axioms spin_total_error
#print axioms halfFalling_22_coefficient
#print axioms spin_order20_error
end
end M14.EulerianSpin
