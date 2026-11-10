import SpecialImaginaryPoint.V14119Priority3ZeroedIndexActualDet
import SpecialImaginaryPoint.V14119Priority3FiniteIntrinsicFunctional

/-!
# Priority 3 — genuine CFC S₁ rank-one perturbations of the intrinsic finite Fredholm determinant

The certified intrinsic Fredholm functional is evaluated on genuine finite
nuclear CFC Schatten-S₁ operators, NOT on a merely formal Gram matrix.
For a finite family u,v, removing the a-th nuclear term is implemented
by setting u_a to zero. The actual operator difference is *exactly*
rankOneS1(u_a,v_a), and its true CFC trace norm is
‖u_a‖ ‖v_a‖.

Combined with the actual Gram determinant inequality in the preceding
module, this establishes a genuine Schatten-S₁ first-order determinant
bound, with exponential dependence only on the remaining nuclear costs.
No dimension factors, normality or invertibility.

Still missing: telescoping arbitrary finite nuclear perturbations with
optimal decompositions and subsequent continuous extension to ALL S₁.
-/

noncomputable section

namespace Manuscript14Priority3.IntrinsicFiniteS1RankOneBound

open Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.ZeroedIndexActualDet

/-- The actual CFC trace-class representation of the zero left vector is zero. -/
theorem rankOneS1_zero_left (v : H) :
    rankOneS1 (0 : H) v = 0 := by
  apply Subtype.ext
  rw [rankOneS1_operator]
  simp

/-- Removing exactly one nuclear vector subtracts EXACTLY the
corresponding true CFC-S₁ rank-one operator (not only its bounded
operator image). -/
theorem finiteNuclear_sub_withoutIndex_eq_rankOne
    {m : ℕ} (u v : Fin m → H) (a : Fin m) :
    finiteNuclear m u v - finiteNuclear m (withoutIndex u a) v =
      rankOneS1 (u a) (v a) := by
  have heach (i : Fin m) :
      rankOneS1 (u i) (v i) -
        rankOneS1 (withoutIndex u a i) (v i) =
      if i = a then rankOneS1 (u a) (v a) else 0 := by
    by_cases hi : i = a
    · subst i
      simp [withoutIndex, rankOneS1_zero_left]
    · simp [withoutIndex, hi]
  calc
    finiteNuclear m u v - finiteNuclear m (withoutIndex u a) v =
      ∑ i : Fin m,
        (rankOneS1 (u i) (v i) -
          rankOneS1 (withoutIndex u a i) (v i)) := by
        simp only [finiteNuclear, Finset.sum_sub_distrib]
    _ = ∑ i : Fin m,
          if i = a then rankOneS1 (u a) (v a) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact heach i
    _ = rankOneS1 (u a) (v a) := by simp

/-- EXACT true CFC Schatten-S₁ trace norm of the one-term perturbation. -/
theorem finiteNuclear_sub_withoutIndex_norm_eq
    {m : ℕ} (u v : Fin m → H) (a : Fin m) :
    ‖finiteNuclear m u v - finiteNuclear m (withoutIndex u a) v‖ =
      ‖u a‖ * ‖v a‖ := by
  rw [finiteNuclear_sub_withoutIndex_eq_rankOne]
  exact rankOneS1_norm_eq (u a) (v a)

/-- One-step dimension-free determinant perturbation for TWO
ACTUAL intrinsic finite-nuclear CFC-S₁ Fredholm functionals. -/
theorem detFinite_one_rankOne_nuclear_cost_norm_le_exp
    {m : ℕ} (u v : Fin m → H) (z : ℂ) (a : Fin m) :
    ‖detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z -
      detFinite (finiteNuclear m (withoutIndex u a) v)
        ⟨canonicalPresentation m (withoutIndex u a) v⟩ z‖ ≤
      (‖z‖ * (‖u a‖ * ‖v a‖)) *
        Real.exp (∑ i ∈ Finset.univ.erase a,
          ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  rw [detFinite_finiteNuclear, detFinite_finiteNuclear]
  exact det_sub_det_withoutIndex_norm_le_exp u v z a

/-- The ACTUAL S₁ trace-norm rank-one perturbation inequality for
the intrinsic finite Fredholm determinant. The norm on the right
is the genuine CFC Schatten-S₁ norm of the difference of the two
finite nuclear operators, not a presentation-only scalar cost. -/
theorem detFinite_one_rankOne_traceNorm_le_exp
    {m : ℕ} (u v : Fin m → H) (z : ℂ) (a : Fin m) :
    ‖detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z -
      detFinite (finiteNuclear m (withoutIndex u a) v)
        ⟨canonicalPresentation m (withoutIndex u a) v⟩ z‖ ≤
      (‖z‖ * ‖finiteNuclear m u v -
        finiteNuclear m (withoutIndex u a) v‖) *
        Real.exp (∑ i ∈ Finset.univ.erase a,
          ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  rw [finiteNuclear_sub_withoutIndex_norm_eq]
  exact detFinite_one_rankOne_nuclear_cost_norm_le_exp u v z a

#print axioms Manuscript14Priority3.IntrinsicFiniteS1RankOneBound.rankOneS1_zero_left
#print axioms Manuscript14Priority3.IntrinsicFiniteS1RankOneBound.finiteNuclear_sub_withoutIndex_eq_rankOne
#print axioms Manuscript14Priority3.IntrinsicFiniteS1RankOneBound.finiteNuclear_sub_withoutIndex_norm_eq
#print axioms Manuscript14Priority3.IntrinsicFiniteS1RankOneBound.detFinite_one_rankOne_nuclear_cost_norm_le_exp
#print axioms Manuscript14Priority3.IntrinsicFiniteS1RankOneBound.detFinite_one_rankOne_traceNorm_le_exp

end Manuscript14Priority3.IntrinsicFiniteS1RankOneBound
