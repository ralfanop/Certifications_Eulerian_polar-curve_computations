import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Manuscript 14.119 Priority 3 — exact finite rank-one resolvent perturbation

For a completely arbitrary complex finite matrix A whose determinant
is nonzero, the matrix determinant lemma produces an *exact* rank-one
perturbation formula. We isolate its scalar correction and exact norm.

This is an algebraic first step toward the nuclear Fredholm determinant
perturbation theorem, NOT a uniform bound. The inverse A⁻¹ may be large,
and the formula here assumes the unperturbed matrix is nonsingular.
Neither difficulty may be discarded in a universal CFC-S₁ extension.
-/

noncomputable section
namespace Manuscript14Priority3.FiniteRankOneResolventUpdate

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite-dimensional resolvent sandwich for complex rank-one
perturbations, represented as a genuine 1×1 complex matrix. -/
def correction (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.replicateRow (Fin 1) v *
    A⁻¹ * Matrix.replicateCol (Fin 1) u

/-- The full exact determinant lemma for arbitrary nonnormal complex
matrices with invertible background, with no positivity hypothesis. -/
theorem det_rankOne_update_of_isUnit (A : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (u v : ι → ℂ) :
    (A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det =
      A.det * (1 + correction A u v).det := by
  exact Matrix.det_add_replicateCol_mul_replicateRow hA u v

/-- EXACT first-order determinant increment with an arbitrary
complex rank-one update, evaluated in its one-dimensional factor. -/
theorem det_rankOne_update_sub_eq (A : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (u v : ι → ℂ) :
    (A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det - A.det =
      A.det * correction A u v 0 0 := by
  rw [det_rankOne_update_of_isUnit A hA u v]
  have h1 : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + correction A u v).det =
      1 + correction A u v 0 0 := by
    rw [Matrix.det_fin_one]
    simp [Matrix.add_apply]
  rw [h1]
  ring

/-- Exact perturbation norm: the nonzero-baseline determinant is
multiplied by the scalar resolvent correction. It is explicitly
NOT the final dimension-uniform trace-norm perturbation inequality. -/
theorem det_rankOne_update_sub_norm_eq (A : Matrix ι ι ℂ)
    (hA : IsUnit A.det) (u v : ι → ℂ) :
    ‖(A + Matrix.replicateCol (Fin 1) u *
        Matrix.replicateRow (Fin 1) v).det - A.det‖ =
      ‖A.det‖ * ‖correction A u v 0 0‖ := by
  rw [det_rankOne_update_sub_eq A hA u v, norm_mul]

#print axioms Manuscript14Priority3.FiniteRankOneResolventUpdate.det_rankOne_update_of_isUnit
#print axioms Manuscript14Priority3.FiniteRankOneResolventUpdate.det_rankOne_update_sub_eq
#print axioms Manuscript14Priority3.FiniteRankOneResolventUpdate.det_rankOne_update_sub_norm_eq

end Manuscript14Priority3.FiniteRankOneResolventUpdate
