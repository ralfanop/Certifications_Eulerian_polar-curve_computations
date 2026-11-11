import SpecialImaginaryPoint.V14119Priority3IntrinsicFiniteS1MultitermBound

/-!
# Priority 3 — exact CFC-S₁ operator difference for arbitrary finite nuclear deletions

For an arbitrary complex Hilbert finite-nuclear operator
T = Σ_i |u_i⟩⟨v_i|, let T_s be the same presentation with u_i = 0
at every i ∈ s. Then *in the actual CFC Schatten S₁ space*:
  T − T_s = Σ_{i∈s} |u_i⟩⟨v_i|.
Consequently,
  ‖T − T_s‖₁ ≤ Σ_{i∈s} ‖u_i‖‖v_i‖.

This links the arbitrary multi-index determinant increment from
the predecessor with the genuine S₁ perturbation, and records the
precise direction of the nuclear-mass bound. It does NOT replace
nuclear presentation cost by exact norm in the determinant upper
bound: that substitution requires optimal finite presentations of
the difference, a separate pending task.
-/

noncomputable section

namespace Manuscript14Priority3.MaskedS1Difference

open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.MultiIndexGramPerturb

/-- The true CFC-S₁ rank-one element is zero if its left vector is
zero, directly from the certified exact rank-one trace norm. -/
theorem rankOneS1_zero_left (v : H) :
    rankOneS1 (0 : H) v = 0 := by
  apply norm_eq_zero.mp
  rw [rankOneS1_norm_eq]
  simp

/-- ACTUAL OPERATOR DIFFERENCE: deleting any finite set of rank-one
terms from a finite CFC-S₁ nuclear presentation subtracts exactly the
finite sum of the deleted genuine Schatten-S₁ rank-one operators. -/
theorem finiteNuclear_sub_zeroOut_eq_finset
    {m : ℕ} (u v : Fin m → H) (s : Finset (Fin m)) :
    finiteNuclear m u v - finiteNuclear m (zeroOut u s) v =
      ∑ i ∈ s, rankOneS1 (u i) (v i) := by
  classical
  have hpoint (i : Fin m) :
      rankOneS1 (u i) (v i) -
        rankOneS1 (zeroOut u s i) (v i) =
      if i ∈ s then rankOneS1 (u i) (v i) else 0 := by
    by_cases hi : i ∈ s
    · simp [zeroOut, hi, rankOneS1_zero_left]
    · simp [zeroOut, hi]
  calc
    finiteNuclear m u v - finiteNuclear m (zeroOut u s) v =
      ∑ i : Fin m,
        (rankOneS1 (u i) (v i) -
          rankOneS1 (zeroOut u s i) (v i)) := by
            simp only [finiteNuclear, Finset.sum_sub_distrib]
    _ = ∑ i : Fin m,
          if i ∈ s then rankOneS1 (u i) (v i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = ∑ i ∈ s, rankOneS1 (u i) (v i) := by
      simp

/-- Actual trace-norm upper bound on the difference of the
two *genuine* Schatten-S₁ operators, without dimension factors. -/
theorem finiteNuclear_sub_zeroOut_norm_le_mass
    {m : ℕ} (u v : Fin m → H) (s : Finset (Fin m)) :
    ‖finiteNuclear m u v - finiteNuclear m (zeroOut u s) v‖ ≤
      ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
  rw [finiteNuclear_sub_zeroOut_eq_finset]
  calc
    ‖∑ i ∈ s, rankOneS1 (u i) (v i)‖ ≤
      ∑ i ∈ s, ‖rankOneS1 (u i) (v i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
      simp only [rankOneS1_norm_eq]

#print axioms Manuscript14Priority3.MaskedS1Difference.rankOneS1_zero_left
#print axioms Manuscript14Priority3.MaskedS1Difference.finiteNuclear_sub_zeroOut_eq_finset
#print axioms Manuscript14Priority3.MaskedS1Difference.finiteNuclear_sub_zeroOut_norm_le_mass

end Manuscript14Priority3.MaskedS1Difference
