import Mathlib

/-!
# Priority 3 — unconditional complex rank-one determinant perturbation

The classical rank-one determinant formula with adjugate/cofactor
contractions works even when the background matrix is singular.
To avoid any division by det(A), we prove it by elementary column
multilinearity and invariance under adding a multiple of one column
to another.

For arbitrary finite complex A, u, v:
  det(A + uvᵀ) - det(A)
    = Σ_j v_j det(A.updateCol j u).

This identity makes no invertibility, positivity, self-adjointness,
normality or dimension hypothesis. It is the missing *algebraic*
singular-background rank-one perturbation step; the dimension-free
trace-norm estimate for this increment remains to be supplied.
-/

noncomputable section

namespace Manuscript14Priority3.RankOneUpdateAllBackgrounds

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Only columns indexed by s receive their rank-one increments. -/
def updatedColumns (s : Finset ι) (A : Matrix ι ι ℂ)
    (u v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => A i j + if j ∈ s then v j * u i else 0

theorem updatedColumns_empty (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    updatedColumns (∅ : Finset ι) A u v = A := by
  ext i j
  simp [updatedColumns]

theorem updatedColumns_univ (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    updatedColumns Finset.univ A u v =
      A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v := by
  ext i j
  simp [updatedColumns, Matrix.add_apply, Matrix.mul_apply,
    Matrix.replicateCol, Matrix.replicateRow, mul_comm]

/-- Insert one modified column into the partial perturbation. -/
theorem updatedColumns_insert (A : Matrix ι ι ℂ) (u v : ι → ℂ)
    (j : ι) (s : Finset ι) (hj : j ∉ s) :
    updatedColumns (insert j s) A u v =
      (updatedColumns s A u v).updateCol j
        (fun i => A i j + v j * u i) := by
  ext i k
  by_cases hkj : k = j
  · subst k
    simp [updatedColumns, hj]
  · simp [updatedColumns, Matrix.updateCol_ne hkj, hkj]

/-- If column j has already been replaced by u, all updates
of the other columns add multiples of that j-column and therefore
leave the determinant exactly invariant. -/
theorem updatedColumns_updateCol_det (A : Matrix ι ι ℂ)
    (u v : ι → ℂ) (s : Finset ι) :
    ∀ j : ι, j ∉ s →
      ((updatedColumns s A u v).updateCol j u).det =
        (A.updateCol j u).det := by
  induction s using Finset.induction_on with
  | empty =>
      intro j hj
      simp [updatedColumns_empty]
  | @insert k s hk ih =>
      intro j hj
      have hkj : k ≠ j := by
        intro h
        apply hj
        rw [← h]
        exact Finset.mem_insert_self k s
      have hjs : j ∉ s := by
        intro h
        exact hj (Finset.mem_insert_of_mem h)
      rw [updatedColumns_insert A u v k s hk]
      rw [Matrix.updateCol_comm (updatedColumns s A u v)
        hkj (fun i => A i k + v k * u i) u]
      have hvector :
          (fun i : ι => A i k + v k * u i) =
            (fun i : ι =>
              ((updatedColumns s A u v).updateCol j u) i k +
                v k * ((updatedColumns s A u v).updateCol j u) i j) := by
        funext i
        simp [updatedColumns, Matrix.updateCol_ne hkj, hk]
      rw [hvector]
      rw [Matrix.det_updateCol_add_smul_self
        ((updatedColumns s A u v).updateCol j u) hkj (v k)]
      exact ih j hjs

/-- A rank-one perturbation affects the determinant only linearly
in each modified column; any term involving two copies of u
vanishes by alternation. -/
theorem updatedColumns_det (A : Matrix ι ι ℂ)
    (u v : ι → ℂ) (s : Finset ι) :
    (updatedColumns s A u v).det =
      A.det + ∑ j ∈ s, v j * (A.updateCol j u).det := by
  induction s using Finset.induction_on with
  | empty =>
      simp [updatedColumns_empty]
  | @insert k s hk ih =>
      rw [updatedColumns_insert A u v k s hk]
      have hself :
          (updatedColumns s A u v).updateCol k (fun i => A i k) =
            updatedColumns s A u v := by
        ext i j
        by_cases h : j = k
        · subst j
          simp [updatedColumns, hk]
        · simp [Matrix.updateCol_ne h]
      have hsmul :
          ((updatedColumns s A u v).updateCol k
              (fun i => v k * u i)).det =
            v k * ((updatedColumns s A u v).updateCol k u).det := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (Matrix.det_updateCol_smul (updatedColumns s A u v) k (v k) u)
      rw [show
        (fun i : ι => A i k + v k * u i) =
          (fun i : ι => A i k) + (fun i : ι => v k * u i) from rfl]
      rw [Matrix.det_updateCol_add, hself, hsmul]
      rw [updatedColumns_updateCol_det A u v s k hk]
      rw [ih, Finset.sum_insert hk]
      ring

/-- Unrestricted complex rank-one determinant lemma, including
SINGULAR background matrices and arbitrary dimensions. -/
theorem det_rankOne_update_without_invertibility
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    (A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det =
      A.det + ∑ j : ι, v j * (A.updateCol j u).det := by
  rw [← updatedColumns_univ A u v]
  exact updatedColumns_det A u v Finset.univ

/-- Exact complex perturbation increment without determinant
or resolvent invertibility assumptions. -/
theorem det_rankOne_update_sub_without_invertibility
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    (A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det - A.det =
      ∑ j : ι, v j * (A.updateCol j u).det := by
  rw [det_rankOne_update_without_invertibility]
  ring

/-- Unconditional norm control by the cofactor-column sum.
The next step is to replace this dimension-dependent expression
with a sharp nuclear mass bound from the mixed-Gram structure. -/
theorem det_rankOne_update_sub_norm_le_cofactors
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    ‖(A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det - A.det‖ ≤
      ∑ j : ι, ‖v j‖ * ‖(A.updateCol j u).det‖ := by
  rw [det_rankOne_update_sub_without_invertibility]
  calc
    ‖∑ j : ι, v j * (A.updateCol j u).det‖ ≤
        ∑ j : ι, ‖v j * (A.updateCol j u).det‖ := norm_sum_le _ _
    _ = ∑ j : ι, ‖v j‖ * ‖(A.updateCol j u).det‖ := by
      simp only [norm_mul]

#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.updatedColumns_univ
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.updatedColumns_insert
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.updatedColumns_updateCol_det
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.updatedColumns_det
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.det_rankOne_update_without_invertibility
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.det_rankOne_update_sub_without_invertibility
#print axioms Manuscript14Priority3.RankOneUpdateAllBackgrounds.det_rankOne_update_sub_norm_le_cofactors

end Manuscript14Priority3.RankOneUpdateAllBackgrounds
