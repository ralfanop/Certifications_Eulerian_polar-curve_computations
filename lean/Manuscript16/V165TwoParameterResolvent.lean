import Manuscript16.V165ResolventMultiplier

/-!
M16 v16.5 §14.1: two-parameter scalar resolvent identity.
Authoritative source ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e

These are scalar identities for b,c>0 and t>=0. They do not establish
an operator resolvent identity or any Schatten/trace statement.
-/

namespace Manuscript16.V165TwoParameter

theorem resolvent_difference (b c t : ℝ)
    (hb : 0 < b) (hc : 0 < c) (ht : 0 ≤ t) :
    1 / (b + t) - 1 / (c + t) =
      (c - b) / ((b + t) * (c + t)) := by
  have hbt : b + t ≠ 0 := ne_of_gt (by linarith)
  have hct : c + t ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem resolvent_difference_abs (b c t : ℝ)
    (hb : 0 < b) (hc : 0 < c) (ht : 0 ≤ t) :
    |1 / (b + t) - 1 / (c + t)| =
      |c - b| / ((b + t) * (c + t)) := by
  have hbt : 0 < b + t := by linarith
  have hct : 0 < c + t := by linarith
  have hprod : 0 < (b + t) * (c + t) := mul_pos hbt hct
  rw [resolvent_difference b c t hb hc ht, abs_div]
  rw [abs_of_pos hprod]

#print axioms Manuscript16.V165TwoParameter.resolvent_difference
#print axioms Manuscript16.V165TwoParameter.resolvent_difference_abs

end Manuscript16.V165TwoParameter
