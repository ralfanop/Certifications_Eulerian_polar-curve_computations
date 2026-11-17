import Mathlib
import Manuscript16.V164MaxwellFiniteCutoff

/-!
M16 v16.5 Section 13, eq. mixed-lower-series-164: at p=3 the actual
infinite nearest-mode numerical series diverges. This is not yet an
operator Schatten theorem; it uses the exact finite arithmetic of #321.
-/
namespace Manuscript16.V165Schatten

noncomputable def thirdShell (n : ℕ) : ℝ :=
  2 * (((n : ℝ) + 2)^2 - 1) / (4 * ((n : ℝ) + 2 + 1))^3

theorem third_shell_nonsummable : ¬ Summable thirdShell := by
  intro hs
  have hlarge : Summable (fun n : ℕ => 96 * thirdShell n) := hs.mul_left 96
  have hle (n : ℕ) : 1 / ((n : ℝ) + 3) ≤ 96 * thirdShell n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h := Manuscript16.v164_maxwell_third_shell_gap_nonneg
      ((n : ℝ) + 2) (by linarith)
    have hd : 0 < (n : ℝ) + 3 := by positivity
    calc
      1 / ((n : ℝ) + 3) =
          96 * (1 / (96 * ((n : ℝ) + 2 + 1))) := by
        rw [show (n : ℝ) + 2 + 1 = (n : ℝ) + 3 by ring]
        field_simp
      _ ≤ 96 * thirdShell n := mul_le_mul_of_nonneg_left h (by norm_num)
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 3)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hlarge
  have hh' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 3| ^ (1 : ℝ)) := by
    convert hh using 1
    funext n
    rw [Real.rpow_one, abs_of_nonneg (by positivity)]
  exact (lt_irrefl (1 : ℝ)) ((Real.summable_one_div_nat_add_rpow 3 1).mp hh')

#print axioms Manuscript16.V165Schatten.third_shell_nonsummable
end Manuscript16.V165Schatten
