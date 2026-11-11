import Mathlib

/-!
# Priority 3 — exact polynomiality and entire holomorphy
# of arbitrary complex finite determinant pencils

For EVERY complex square matrix M of every finite size (singular,
nonselfadjoint, nonnormal allowed) the function
   z ↦ det(I + z M)
is the evaluation of the genuine complex polynomial
   det(I + X M)
and hence is ENTIRE on ℂ.

This is the universal finite-dimensional analytic prerequisite
for Weierstrass' theorem applied to the true Hilbert compression
determinants, and it never requires invertibility or spectral
decomposition.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteShiftEntirePolynomial

open Matrix Polynomial
open scoped Ring

/-- The exact finite complex polynomial underlying the
whole spectral determinant pencil. -/
def determinantPolynomial (N : ℕ)
    (M : Matrix (Fin N) (Fin N) ℂ) : ℂ[X] :=
  Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)

/-- Evaluation of the polynomial determinant is the genuine
matrix determinant at any arbitrary complex z. -/
theorem determinantPolynomial_eval (N : ℕ)
    (M : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    (determinantPolynomial N M).eval z =
      (1 + z • M).det := by
  unfold determinantPolynomial
  rw [eval_det, matPolyEquiv_eval_eq_map]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]

/-- Every finite matrix spectral determinant is ENTIRE.
This is unconditional for singular and nonnormal matrices. -/
theorem determinant_shift_entire (N : ℕ)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    Differentiable ℂ (fun z : ℂ => (1 + z • M).det) := by
  have h : (fun z : ℂ => (1 + z • M).det) =
      (fun z : ℂ => (determinantPolynomial N M).eval z) := by
    funext z
    exact (determinantPolynomial_eval N M z).symm
  rw [h]
  exact (determinantPolynomial N M).differentiable

#print axioms Manuscript14Priority3.FiniteShiftEntirePolynomial.determinantPolynomial_eval
#print axioms Manuscript14Priority3.FiniteShiftEntirePolynomial.determinant_shift_entire

end Manuscript14Priority3.FiniteShiftEntirePolynomial
