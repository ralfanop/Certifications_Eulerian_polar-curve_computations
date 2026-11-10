import SpecialImaginaryPoint.V14119Priority3FiniteGramOneStepDet

/-!
# Priority 3 — identify the omitted principal-minor expansion with
# a genuine complex Fredholm determinant

The omitted-index expression in PR #119 is the determinant of the
same mixed-Gram family with the corresponding left nuclear vector
replaced by zero.  This removes the remaining algebraic placeholder
from the one-step determinant perturbation estimate.

The proof partitions the full principal-minor powerset into subsets
containing the distinguished index and subsets not containing it.
Minors in the first class vanish by an actual zero column; all
remaining minors are literally equal to the unmodified Gram minors.

No positivity, normality, invertibility, or matrix dimension
assumption.  The full multi-term trace-norm inequality and the
global continuous determinant on S₁ remain separate obligations.
-/

noncomputable section

namespace Manuscript14Priority3.ZeroedIndexActualDet

open Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.MinorExpansionIncrement
open Manuscript14Priority3.WeightedGramMinorStep
open Manuscript14Priority3.ExactGramPrincipalExpansion
open Manuscript14Priority3.FiniteGramOneStepDet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Set precisely one left nuclear vector to zero, without
changing the original family length or any other vector. -/
def withoutIndex {m : ℕ} (u : Fin m → E) (a : Fin m) : Fin m → E :=
  fun j => if j = a then 0 else u j

/-- Every Gram minor omitting a is unchanged if u_a becomes zero. -/
theorem weightedGramMinor_withoutIndex_eq_of_not_mem {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (a : Fin m)
    (s : Finset (Fin m)) (ha : a ∉ s) :
    weightedGramMinor (withoutIndex u a) v z s =
      weightedGramMinor u v z s := by
  have hm :
      (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (withoutIndex u a) v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m) =
      (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        u v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m) := by
    ext i j
    have hj : (j : Fin m) ≠ a := by
      intro heq
      exact ha (heq ▸ j.property)
    change inner ℂ (v (i : Fin m)) (withoutIndex u a (j : Fin m)) =
      inner ℂ (v (i : Fin m)) (u (j : Fin m))
    simp [withoutIndex, hj]
  simp only [weightedGramMinor, hm]

/-- Every principal minor containing a has an actual zero column
when u_a has been replaced by zero. -/
theorem weightedGramMinor_withoutIndex_eq_zero_of_mem {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (a : Fin m)
    (s : Finset (Fin m)) (ha : a ∈ s) :
    weightedGramMinor (withoutIndex u a) v z s = 0 := by
  have hdet :
      ((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (withoutIndex u a) v).submatrix
        (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero (⟨a, ha⟩ : s)
    intro i
    change inner ℂ (v (i : Fin m)) (withoutIndex u a a) = 0
    simp [withoutIndex]
  simp [weightedGramMinor, hdet]

/-- The omitted-index principal-minor expansion is exactly the
ACTUAL finite-dimensional determinant of the rank-one family with
this index removed (implemented by a zero nuclear vector). -/
theorem omitted_index_expansion_eq_zeroed_det {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (a : Fin m) :
    principalExpansion (weightedGramMinor u v z)
      (Finset.univ.erase a) =
    (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
      (withoutIndex u a) v).det := by
  let s : Finset (Fin m) := Finset.univ.erase a
  have ha : a ∉ s := by simp [s]
  have hs : insert a s = Finset.univ := by
    simpa [s] using (Finset.insert_erase (Finset.mem_univ a))
  have h := weightedGram_full_expansion_eq_det (withoutIndex u a) v z
  change (∑ t ∈ (Finset.univ : Finset (Fin m)).powerset,
      weightedGramMinor (withoutIndex u a) v z t) = _ at h
  rw [← hs, Finset.sum_powerset_insert ha] at h
  have hkeep :
      (∑ t ∈ s.powerset,
        weightedGramMinor (withoutIndex u a) v z t) =
        principalExpansion (weightedGramMinor u v z) s := by
    unfold principalExpansion
    apply Finset.sum_congr rfl
    intro t ht
    apply weightedGramMinor_withoutIndex_eq_of_not_mem u v z a t
    intro hat
    exact ha ((Finset.mem_powerset.mp ht) hat)
  have hdrop :
      (∑ t ∈ s.powerset,
        weightedGramMinor (withoutIndex u a) v z (insert a t)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    apply weightedGramMinor_withoutIndex_eq_zero_of_mem
    exact Finset.mem_insert_self a t
  rw [hkeep, hdrop, add_zero] at h
  exact h

/-- The genuine full complex determinant is Lipschitz to first
order in one rank-one nuclear term; BOTH sides of the difference
are honest determinants, even at singular and nonnormal matrices.
The exponential majorant is independent of m. -/
theorem det_sub_det_withoutIndex_norm_le_exp {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (a : Fin m) :
    ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det -
      (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (withoutIndex u a) v).det‖ ≤
      (‖z‖ * (‖u a‖ * ‖v a‖)) *
        Real.exp (∑ i ∈ Finset.univ.erase a,
          ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  rw [← omitted_index_expansion_eq_zeroed_det u v z a]
  exact full_det_sub_omitted_index_expansion_norm_le u v z a

#print axioms Manuscript14Priority3.ZeroedIndexActualDet.weightedGramMinor_withoutIndex_eq_of_not_mem
#print axioms Manuscript14Priority3.ZeroedIndexActualDet.weightedGramMinor_withoutIndex_eq_zero_of_mem
#print axioms Manuscript14Priority3.ZeroedIndexActualDet.omitted_index_expansion_eq_zeroed_det
#print axioms Manuscript14Priority3.ZeroedIndexActualDet.det_sub_det_withoutIndex_norm_le_exp

end Manuscript14Priority3.ZeroedIndexActualDet
