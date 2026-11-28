import Mathlib
import Manuscript17.StrongCycleGeneral20261127

noncomputable section
namespace Manuscript17.StrongCycleChebyshev

open Polynomial Finset
open Polynomial.Chebyshev

def angle (n : ℕ) (i : Fin (n+2)) : ℝ :=
  ((i.val : ℝ) + 1/2) * Real.pi / (n+2)

def alpha (n : ℕ) (i : Fin (n+2)) : ℂ :=
  (Real.cos (angle n i) : ℂ)

def radius (n : ℕ) : ℂ :=
  (((1/2 : ℝ) ^ ((n+1 : ℝ)/(n+2))) : ℂ)

theorem angle_mem (n : ℕ) (i : Fin (n+2)) :
    angle n i ∈ Set.Ioo (0:ℝ) Real.pi := by
  have hn : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hi : (i.val : ℝ) < (n:ℝ)+2 := by exact_mod_cast i.isLt
  have hi' : (i.val : ℝ) + 1/2 < (n:ℝ)+2 := by
    have h : i.val ≤ n+1 := by omega
    have h' : (i.val:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast h
    linarith
  constructor
  · unfold angle
    positivity
  · unfold angle
    apply (div_lt_iff₀ hn).2
    nlinarith [mul_pos (sub_pos.mpr hi') Real.pi_pos]

theorem alpha_injective (n : ℕ) : Function.Injective (alpha n) := by
  intro i j h
  have he : Real.cos (angle n i) = Real.cos (angle n j) := by exact_mod_cast h
  have hi := angle_mem n i
  have hj := angle_mem n j
  have ha : angle n i = angle n j :=
    Real.strictAntiOn_cos.injOn ⟨hi.1.le,hi.2.le⟩ ⟨hj.1.le,hj.2.le⟩ he
  unfold angle at ha
  have hn : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hm := (div_left_inj' hn.ne').mp ha
  have hval := (mul_right_cancel₀ Real.pi_pos.ne' hm)
  apply Fin.ext
  exact_mod_cast (show (i.val:ℝ) = (j.val:ℝ) by linarith)

theorem alpha_root (n : ℕ) (i : Fin (n+2)) :
    (T ℂ (n+2 : ℤ)).eval (alpha n i) = 0 := by
  have hden : (n:ℝ)+2 ≠ 0 := by positivity
  have hangle : ((n+2:ℤ):ℝ) * angle n i =
      Real.pi/2 + (i.val:ℝ)*Real.pi := by
    unfold angle
    push_cast
    field_simp [hden]
    <;> ring
  have hr : (T ℝ (n+2 : ℤ)).eval (Real.cos (angle n i)) = 0 := by
    rw [T_real_cos, hangle, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]
  simpa only [alpha, ← complex_ofReal_eval_T, Complex.ofReal_eq_zero] using hr

theorem concrete_factor (n : ℕ) (z : ℂ) :
    (∏ i : Fin (n+2), (z-alpha n i)) =
      (T ℂ (n+2 : ℤ)).eval z / (2:ℂ)^(n+1) := by
  classical
  let p := T ℂ (n+2 : ℤ)
  let e : Fin (n+2) ↪ ℂ := ⟨alpha n, alpha_injective n⟩
  let S : Finset ℂ := Finset.univ.map e
  have hdeg : p.degree = (n+2 : ℕ) := by
    dsimp [p]
    rw [degree_T]
    norm_cast
  have hc : (S.card : WithBot ℕ) = p.degree := by
    rw [hdeg]
    simp [S]
  have hr : p.roots = S.val := by
    apply roots_eq_of_degree_eq_card _ hc
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact alpha_root n i
  have hl : p.leadingCoeff = (2:ℂ)^(n+1) := by
    dsimp [p]
    rw [leadingCoeff_T]
    congr 1
    omega
  have hf := (IsAlgClosed.splits p).eval_eq_prod_roots z
  rw [hr, hl] at hf
  have hprod : (S.val.map (fun x => z-x)).prod = ∏ i : Fin (n+2), (z-alpha n i) := by
    change (∏ x ∈ S, (z-x)) = _
    simp [S, e, Finset.prod_map]
  rw [hprod] at hf
  change _ = p.eval z / (2:ℂ)^(n+1)
  rw [hf]
  field_simp

theorem radius_power (n : ℕ) :
    radius n ^ (n+2) = 1/(2:ℂ)^(n+1) := by
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  have he : ((n+1:ℝ)/(n+2)) * (n+2:ℕ) = (n+1:ℕ) := by
    push_cast
    field_simp [hn]
  have h : ((1/2:ℝ)^((n+1:ℝ)/(n+2)))^(n+2:ℕ) = 1/(2:ℝ)^(n+1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (1/2:ℝ)), he, Real.rpow_natCast, div_pow, one_pow]
  exact_mod_cast h

theorem radius_ne_zero (n : ℕ) : radius n ≠ 0 := by
  have h := radius_power n
  intro hz
  rw [hz, zero_pow (by omega : n+2 ≠ 0)] at h
  exact (div_ne_zero one_ne_zero (pow_ne_zero _ (by norm_num))).symm h

/-- No root-factorization or radius-normalization premise. -/
theorem concrete_determinant (n : ℕ) (w z : ℂ) :
    (Manuscript17.StrongCycle.pencil n (fun i => z-alpha n i) (radius n) w).det =
      ((T ℂ (n+2 : ℤ)).eval z-w)/(2:ℂ)^(n+1) := by
  exact Manuscript17.StrongCycle.chebyshev_determinant n (alpha n) (radius n) w z
    (radius_power n) (concrete_factor n z)

#print axioms angle_mem
#print axioms alpha_injective
#print axioms alpha_root
#print axioms concrete_factor
#print axioms radius_power
#print axioms radius_ne_zero
#print axioms concrete_determinant
end Manuscript17.StrongCycleChebyshev
