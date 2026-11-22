import EulerianCert.Bracket
import Mathlib.Tactic

/-! PRIVATE: exact recurrence-based checks for Manuscript 15, Theorem 7.3. -/
namespace PrivateApex
open EulerianCert.Bracket

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def centralIndex (n : ℕ) : ℕ := (n - 1) / 2
noncomputable def d (n : ℕ) : ℕ :=
  (n + 1) * (E n (centralIndex n) - E n (centralIndex n - 1))

noncomputable def slopeQ (n : ℕ) : ℚ :=
  (n + 1 : ℚ) * ((E n (centralIndex n) : ℚ) - E n (centralIndex n - 1)) /
    n.factorial

/-- All 34 even orders, checked by reduction in the Lean kernel. -/
theorem finite_even_comparisons : ∀ i : Fin 34, let n := 2 * (i.val + 2)
    E n (centralIndex n - 1) < E n (centralIndex n) ∧
    (if n = 12 then 3628800 * d n = 9473633 * n.factorial
     else 3628800 * d n < 9473633 * n.factorial) ∧
    (2 * n.factorial < d n ↔ n ≤ 48) ∧
    (50 ≤ n → d n < 2 * n.factorial) := by
  decide +kernel

/-- The rational statement itself, not merely externally supplied numerators. -/
theorem finite_even_rationals : ∀ i : Fin 34, let n := 2 * (i.val + 2)
    0 < slopeQ n ∧
    (slopeQ n = 9473633 / 3628800 ↔ n = 12) ∧
    slopeQ n ≤ 9473633 / 3628800 ∧
    (2 < slopeQ n ↔ n ≤ 48) ∧
    (50 ≤ n → slopeQ n < 2) := by
  decide +kernel

/-- Extra finite checks for the odd family, through n=71. -/
theorem finite_odd_rationals : ∀ i : Fin 35, let n := 2 * i.val + 3
    0 < slopeQ n ∧ slopeQ n ≤ 2 ∧ (slopeQ n = 2 ↔ n = 3 ∨ n = 5) := by
  decide +kernel

theorem peak_exact : slopeQ 12 = 9473633 / 3628800 := by decide +kernel

theorem peak_above_two : (2 : ℚ) < 9473633 / 3628800 := by norm_num

theorem gaussian_tail_rational_gap : (288 / 73 : ℚ) < (199 / 100) ^ 2 := by norm_num

theorem algebraic_tail_rational_gap :
    (8 * 73 / (72 * 3 ^ 73) : ℚ) < 1 / 100 := by norm_num

#print axioms finite_even_comparisons
#print axioms finite_even_rationals
#print axioms finite_odd_rationals
#print axioms peak_exact
#print axioms peak_above_two
#print axioms gaussian_tail_rational_gap
#print axioms algebraic_tail_rational_gap
end PrivateApex
