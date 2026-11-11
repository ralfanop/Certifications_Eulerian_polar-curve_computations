/-
Manuscript 15: exact rational ratio of successive terms in the inverse
type-B central-binomial series. This module proves algebraic positivity
and the uniform ratio bound used to control the Arb truncation tail.
The full beta-integral and infinite-series identity remain separate.
-/
import Mathlib

noncomputable section
namespace Manuscript15

/-- Exact recurrence ratio for the Sprugnoli inverse-binomial series at u=1/5. -/
def typeBTermRatio (k : ℕ) : ℝ :=
  2 * ((k : ℝ) + 1) / (5 * (2 * (k : ℝ) + 3))

theorem typeBTermRatio_pos (k : ℕ) : 0 < typeBTermRatio k := by
  unfold typeBTermRatio
  positivity

/-- Every exact term ratio lies strictly below 1/5, for all k≥0. -/
theorem typeBTermRatio_lt_fifth (k : ℕ) :
    typeBTermRatio k < (1 / 5 : ℝ) := by
  unfold typeBTermRatio
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) < 5 * (2 * (k : ℝ) + 3) := by positivity
  apply (div_lt_iff₀ hd).2
  nlinarith

/-- This exact positivity implies geometric domination of the tail. -/
def typeBTerm : ℕ → ℝ
  | 0 => 1
  | k + 1 => typeBTerm k * typeBTermRatio k

theorem typeBTerm_pos (k : ℕ) : 0 < typeBTerm k := by
  induction k with
  | zero => norm_num [typeBTerm]
  | succ n ih =>
      change 0 < typeBTerm n * typeBTermRatio n
      exact mul_pos ih (typeBTermRatio_pos n)

theorem typeBTerm_decay (k : ℕ) :
    typeBTerm (k + 1) < typeBTerm k / 5 := by
  calc
    typeBTerm (k + 1) = typeBTerm k * typeBTermRatio k := rfl
    _ < typeBTerm k * (1 / 5 : ℝ) :=
        mul_lt_mul_of_pos_left (typeBTermRatio_lt_fifth k) (typeBTerm_pos k)
    _ = typeBTerm k / 5 := by ring

#print axioms Manuscript15.typeBTermRatio_pos
#print axioms Manuscript15.typeBTermRatio_lt_fifth
#print axioms Manuscript15.typeBTerm_pos
#print axioms Manuscript15.typeBTerm_decay

end Manuscript15
