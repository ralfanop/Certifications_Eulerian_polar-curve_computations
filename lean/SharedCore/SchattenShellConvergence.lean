import Mathlib

/-!
Shared 11–16 core: exact scalar shell comparison for the dimension-three
diagonal regression fixture. This is not yet a Hilbert-space Schatten
membership theorem, nor an identification with the Maxwell operator.
-/
namespace SharedCore.SchattenFredholm

noncomputable def fourthTerm (a : ℝ) : ℝ := (a - 1) / a ^ 3
noncomputable def fourthShell (n : ℕ) : ℝ := fourthTerm ((n : ℝ) + 2)
noncomputable def thirdShell (n : ℕ) : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 2

theorem fourth_shell_nonneg (n : ℕ) : 0 ≤ fourthShell n := by
  unfold fourthShell fourthTerm
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply div_nonneg (by linarith) (by positivity)

theorem fourth_shell_le_square (n : ℕ) :
    fourthShell n ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
  unfold fourthShell fourthTerm
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    ((n : ℝ) + 2 - 1) * ((n : ℝ) + 2) ^ 2 ≤
        ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = 1 * ((n : ℝ) + 2) ^ 3 := by ring

theorem fourth_shell_summable : Summable fourthShell := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 2 2).mpr (by norm_num)
  have hlarge : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
    convert hp using 1
    funext n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
  exact Summable.of_nonneg_of_le fourth_shell_nonneg fourth_shell_le_square hlarge

theorem third_shell_lower (n : ℕ) :
    1 / (2 * ((n : ℝ) + 2)) ≤ thirdShell n := by
  unfold thirdShell
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have h : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h (show 0 ≤ (n : ℝ) + 2 by positivity)]

theorem third_shell_nonsummable : ¬ Summable thirdShell := by
  intro hs
  have hh : Summable (fun n : ℕ => 2 * thirdShell n) := hs.mul_left 2
  have hle (n : ℕ) : 1 / ((n : ℝ) + 2) ≤ 2 * thirdShell n := by
    calc
      1 / ((n : ℝ) + 2) = 2 * (1 / (2 * ((n : ℝ) + 2))) := by
        field_simp
      _ ≤ 2 * thirdShell n := mul_le_mul_of_nonneg_left (third_shell_lower n) (by norm_num)
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hh
  have hsum' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (1 : ℝ)) := by
    convert hsum using 1
    funext n
    rw [Real.rpow_one, abs_of_nonneg (by positivity)]
  exact (lt_irrefl (1 : ℝ)) ((Real.summable_one_div_nat_add_rpow 2 1).mp hsum')

theorem fourth_term_le_telescope (a : ℝ) (ha : 2 ≤ a) :
    fourthTerm a ≤ 1 / a - 1 / (a + 1) := by
  unfold fourthTerm
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a + 1 := by linarith
  rw [show 1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) by
    field_simp <;> ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem fourth_finite_tail_bound (a : ℝ) (ha : 2 ≤ a) (k : ℕ) :
    (∑ i ∈ Finset.range k, fourthTerm (a + (i : ℝ))) ≤
      1 / a - 1 / (a + (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hk : 2 ≤ a + (k : ℝ) := by
      have h : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hstep := fourth_term_le_telescope (a + (k : ℝ)) hk
    rw [← add_assoc]
    linarith

theorem fourth_shell_zeta_difference (n : ℕ) :
    fourthShell n = 1 / ((n : ℝ) + 2) ^ 2 -
      1 / ((n : ℝ) + 2) ^ 3 := by
  unfold fourthShell fourthTerm
  have h : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp <;> ring

#print axioms SharedCore.SchattenFredholm.fourth_shell_nonneg
#print axioms SharedCore.SchattenFredholm.fourth_shell_le_square
#print axioms SharedCore.SchattenFredholm.fourth_shell_summable
#print axioms SharedCore.SchattenFredholm.third_shell_lower
#print axioms SharedCore.SchattenFredholm.third_shell_nonsummable
#print axioms SharedCore.SchattenFredholm.fourth_term_le_telescope
#print axioms SharedCore.SchattenFredholm.fourth_finite_tail_bound
#print axioms SharedCore.SchattenFredholm.fourth_shell_zeta_difference
end SharedCore.SchattenFredholm
