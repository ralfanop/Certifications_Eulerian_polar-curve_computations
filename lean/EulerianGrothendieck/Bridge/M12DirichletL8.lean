import Mathlib

/-!
# Manuscript 12, Appendix A: the positive-discriminant character modulo 8
and the exact rational integral underlying its Dirichlet L-value at 1.

The analytic identification with Mathlib's LFunction at s = 1 is a separate
remaining obligation. This file proves the finite character and integral.
-/
namespace M12.DirichletL8

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MeasureTheory intervalIntegral

def chi8Int (a : ZMod 8) : ℤ :=
  if a.val = 1 ∨ a.val = 7 then 1
  else if a.val = 3 ∨ a.val = 5 then -1 else 0

theorem chi8Int_mul (a b : ZMod 8) :
    chi8Int (a * b) = chi8Int a * chi8Int b := by
  have h : ∀ u v : ZMod 8, chi8Int (u * v) = chi8Int u * chi8Int v := by decide
  exact h a b

theorem chi8Int_nonunit (a : ZMod 8) (ha : ¬ IsUnit a) : chi8Int a = 0 := by
  have hcop : ¬ a.val.Coprime 8 := by
    intro h
    apply ha
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val 8).2 h
  have h : ∀ a : ZMod 8, ¬ a.val.Coprime 8 → chi8Int a = 0 := by decide
  exact h a hcop

def chi8 : DirichletCharacter ℂ 8 where
  toFun a := (chi8Int a : ℂ)
  map_one' := by norm_num [chi8Int]
  map_mul' a b := by rw [chi8Int_mul, Int.cast_mul]
  map_nonunit' a ha := by rw [chi8Int_nonunit a ha, Int.cast_zero]

theorem chi8_values :
    chi8 0 = 0 ∧ chi8 1 = 1 ∧ chi8 2 = 0 ∧ chi8 3 = -1 ∧
    chi8 4 = 0 ∧ chi8 5 = -1 ∧ chi8 6 = 0 ∧ chi8 7 = 1 := by
  change (chi8Int 0 : ℂ) = 0 ∧ (chi8Int 1 : ℂ) = 1 ∧
    (chi8Int 2 : ℂ) = 0 ∧ (chi8Int 3 : ℂ) = -1 ∧
    (chi8Int 4 : ℂ) = 0 ∧ (chi8Int 5 : ℂ) = -1 ∧
    (chi8Int 6 : ℂ) = 0 ∧ (chi8Int 7 : ℂ) = 1
  norm_num [chi8Int, ZMod.val_natCast]

def A (x : ℝ) : ℝ := x^2 + Real.sqrt 2 * x + 1
def B (x : ℝ) : ℝ := x^2 - Real.sqrt 2 * x + 1
def primitive (x : ℝ) : ℝ :=
  (Real.log (A x) - Real.log (B x)) / (2 * Real.sqrt 2)

theorem A_pos (x : ℝ) : 0 < A x := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold A
  nlinarith [sq_nonneg (x + Real.sqrt 2 / 2)]

theorem B_pos (x : ℝ) : 0 < B x := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold B
  nlinarith [sq_nonneg (x - Real.sqrt 2 / 2)]

theorem A_mul_B (x : ℝ) : A x * B x = 1 + x^4 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    A x * B x = (x^2 + 1)^2 - (Real.sqrt 2)^2 * x^2 := by unfold A B; ring
    _ = 1 + x^4 := by rw [hs]; ring

theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive ((1 - x^2) / (1 + x^4)) x := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hA : HasDerivAt A (2*x + Real.sqrt 2) x := by
    unfold A
    convert (((hasDerivAt_pow 2 x).add
      ((hasDerivAt_id x).const_mul (Real.sqrt 2))).add_const 1) using 1 <;> ring
  have hB : HasDerivAt B (2*x - Real.sqrt 2) x := by
    unfold B
    convert (((hasDerivAt_pow 2 x).sub
      ((hasDerivAt_id x).const_mul (Real.sqrt 2))).add_const 1) using 1 <;> ring
  have h := (((hA.log (A_pos x).ne').sub (hB.log (B_pos x).ne')).div_const
    (2 * Real.sqrt 2))
  have hd : ((2*x + Real.sqrt 2) / A x - (2*x - Real.sqrt 2) / B x) /
      (2 * Real.sqrt 2) = (1 - x^2) / (1 + x^4) := by
    rw [← A_mul_B x]
    field_simp [(A_pos x).ne', (B_pos x).ne', hs.ne'] <;> unfold A B <;> ring
  rw [← hd]
  exact h

theorem primitive_zero : primitive 0 = 0 := by norm_num [primitive, A, B]

theorem primitive_one : primitive 1 = Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : 0 < 2 - Real.sqrt (2 : ℝ) := by nlinarith
  have ha1 : A 1 = 2 + Real.sqrt 2 := by unfold A; ring
  have hb1 : B 1 = 2 - Real.sqrt 2 := by unfold B; ring
  have hratio : (2 + Real.sqrt 2) / (2 - Real.sqrt 2) = (1 + Real.sqrt 2)^2 := by
    apply (div_eq_iff hb.ne').2
    have hc : (Real.sqrt 2)^3 = 2 * Real.sqrt 2 := by
      calc
        (Real.sqrt 2)^3 = (Real.sqrt 2)^2 * Real.sqrt 2 := by ring
        _ = _ := by rw [hsq]
    nlinarith
  have ha : (2 + Real.sqrt (2 : ℝ)) ≠ 0 := by positivity
  unfold primitive
  rw [ha1, hb1, ← Real.log_div ha hb.ne', hratio, Real.log_pow]
  norm_num
  <;> field_simp [hs.ne'] <;> ring

theorem integral_value :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - x^2) / (1 + x^4)) =
      Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
  have hc : Continuous (fun x : ℝ => (1 - x^2) / (1 + x^4)) :=
    (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 4)) (fun x => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt x) (hc.intervalIntegrable 0 1),
    primitive_one, primitive_zero, sub_zero]

end

#print axioms M12.DirichletL8.chi8
#print axioms M12.DirichletL8.chi8_values
#print axioms M12.DirichletL8.primitive_hasDerivAt
#print axioms M12.DirichletL8.integral_value

end M12.DirichletL8
