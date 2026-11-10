import SpecialImaginaryPoint.V14119Priority3ZeroedIndexActualDet

/-!
# Priority 3 — simultaneous finite nuclear deletions, dimension-free determinant bound

This is the rigorous finite-step telescoping of the certified
one-rank-one complex mixed-Gram determinant perturbation theorem.
For an arbitrary set s of nuclear indices, replace all u_i for
i∈s by zero (without changing the ambient finite index type).

The genuine complex determinants obey
  |det(I+z G(u,v)) − det(I+z G(zeroOut(u,s),v))|
    ≤ (|z| Σ_{i∈s} ‖u_i‖‖v_i‖)
       exp(|z| Σ_i ‖u_i‖‖v_i‖).
No constants involving dimension, no factorials, and no assumptions
of positivity, normality, selfadjointness or invertibility.

The next operatorial step is to identify the two determinant values
with the presentation-independent intrinsic CFC-S₁ finite-rank
functional, and optimize nuclear costs in the true trace norm.
-/

noncomputable section

namespace Manuscript14Priority3.MultiIndexGramPerturb

open Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.ZeroedIndexActualDet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Erase all terms indexed by s, by zeroing their left vectors. -/
def zeroOut {m : ℕ} (u : Fin m → E) (s : Finset (Fin m)) :
    Fin m → E := fun i => if i ∈ s then 0 else u i

/-- Zeroing a new index is the same as adding that index to the
previously erased set. -/
theorem zeroOut_insert {m : ℕ} (u : Fin m → E)
    (s : Finset (Fin m)) (a : Fin m) :
    zeroOut u (insert a s) = withoutIndex (zeroOut u s) a := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [zeroOut, withoutIndex]
  · by_cases his : i ∈ s
    · simp [zeroOut, withoutIndex, hia, his]
    · simp [zeroOut, withoutIndex, hia, his]

/-- The norm of a masked nuclear vector never exceeds its original norm. -/
theorem zeroOut_norm_le {m : ℕ} (u : Fin m → E)
    (s : Finset (Fin m)) (i : Fin m) :
    ‖zeroOut u s i‖ ≤ ‖u i‖ := by
  by_cases hi : i ∈ s
  · simp [zeroOut, hi]
  · simp [zeroOut, hi]

/-- The TRUE determinants before and after deleting ANY FINITE
collection of nuclear terms satisfy a dimension-independent
multi-term estimate, proved by telescoping certified exact
one-term determinant perturbations. -/
theorem det_sub_det_zeroOut_norm_le_exp {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (s : Finset (Fin m)) :
    ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det -
      (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (zeroOut u s) v).det‖ ≤
      (∑ i ∈ s, ‖z‖ * (‖u i‖ * ‖v i‖)) *
        Real.exp (∑ i : Fin m, ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  let c : Fin m → ℝ := fun i => ‖z‖ * (‖u i‖ * ‖v i‖)
  let M : ℝ := ∑ i : Fin m, c i
  change ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
      u v).det -
    (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
      (zeroOut u s) v).det‖ ≤ (∑ i ∈ s, c i) * Real.exp M
  induction s using Finset.induction_on with
  | empty =>
      have hz : zeroOut u (∅ : Finset (Fin m)) = u := by
        funext i
        simp [zeroOut]
      simp [hz]
  | @insert a s ha ih =>
      have hmass :
          (∑ i ∈ (Finset.univ.erase a : Finset (Fin m)),
            ‖z‖ * (‖zeroOut u s i‖ * ‖v i‖)) ≤ M := by
        calc
          (∑ i ∈ (Finset.univ.erase a : Finset (Fin m)),
            ‖z‖ * (‖zeroOut u s i‖ * ‖v i‖)) ≤
              ∑ i ∈ (Finset.univ.erase a : Finset (Fin m)), c i := by
            apply Finset.sum_le_sum
            intro i hi
            have hnorm := zeroOut_norm_le u s i
            have hprod :
                ‖zeroOut u s i‖ * ‖v i‖ ≤ ‖u i‖ * ‖v i‖ :=
              mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
          _ ≤ M := by
            dsimp [M]
            exact Finset.sum_le_univ_sum_of_nonneg
              (fun i => by dsimp [c]; positivity)
      have hExp : Real.exp
          (∑ i ∈ (Finset.univ.erase a : Finset (Fin m)),
            ‖z‖ * (‖zeroOut u s i‖ * ‖v i‖)) ≤ Real.exp M :=
        Real.exp_le_exp.mpr hmass
      have hkeep : zeroOut u s a = u a := by
        simp [zeroOut, ha]
      have hstep :
          ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
              (zeroOut u s) v).det -
            (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
              (zeroOut u (insert a s)) v).det‖ ≤
          c a * Real.exp M := by
        have hsingle :=
          det_sub_det_withoutIndex_norm_le_exp (zeroOut u s) v z a
        rw [← zeroOut_insert u s a] at hsingle
        calc
          ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
              (zeroOut u s) v).det -
            (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
              (zeroOut u (insert a s)) v).det‖ ≤
            (‖z‖ * (‖zeroOut u s a‖ * ‖v a‖)) *
            Real.exp (∑ i ∈ (Finset.univ.erase a : Finset (Fin m)),
              ‖z‖ * (‖zeroOut u s i‖ * ‖v i‖)) := hsingle
          _ = c a * Real.exp
              (∑ i ∈ (Finset.univ.erase a : Finset (Fin m)),
                ‖z‖ * (‖zeroOut u s i‖ * ‖v i‖)) := by
              rw [hkeep]
          _ ≤ c a * Real.exp M :=
              mul_le_mul_of_nonneg_left hExp (by dsimp [c]; positivity)
      let A : ℂ :=
        (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det
      let B : ℂ :=
        (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
          (zeroOut u s) v).det
      let C : ℂ :=
        (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
          (zeroOut u (insert a s)) v).det
      change ‖A - C‖ ≤ (∑ i ∈ insert a s, c i) * Real.exp M
      calc
        ‖A - C‖ = ‖(A - B) + (B - C)‖ := by congr 1; ring
        _ ≤ ‖A - B‖ + ‖B - C‖ := norm_add_le _ _
        _ ≤ (∑ i ∈ s, c i) * Real.exp M +
              c a * Real.exp M := add_le_add ih hstep
        _ = (∑ i ∈ insert a s, c i) * Real.exp M := by
          rw [Finset.sum_insert ha]
          ring

#print axioms Manuscript14Priority3.MultiIndexGramPerturb.zeroOut_insert
#print axioms Manuscript14Priority3.MultiIndexGramPerturb.zeroOut_norm_le
#print axioms Manuscript14Priority3.MultiIndexGramPerturb.det_sub_det_zeroOut_norm_le_exp

end Manuscript14Priority3.MultiIndexGramPerturb
