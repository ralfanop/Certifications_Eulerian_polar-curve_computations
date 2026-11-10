import SpecialImaginaryPoint.V14119Priority3SharpPolynomialMass
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Priority 3 — entire exponential bound for the finite nuclear Fredholm determinant

Using the sharp coefficient ℓ¹ theorem and the exact polynomial
degree bound, show that every finite mixed complex Gram determinant
obeys the dimension-free *pointwise* exponential envelope in the
complex parameter z, without any normality or positivity restrictions.

The operatorial trace-norm perturbation inequality and S₁ extension
are the separate subsequent proof obligations.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteGramEntireGrowth

open Matrix Polynomial
open scoped InnerProductSpace Ring
open Manuscript14Priority3.SharpPolynomialMass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The determinant polynomial has degree at most the finite nuclear
presentation length. No assumptions on the mixed Gram entries. -/
theorem gramPolynomial_natDegree_le {m : ℕ} (u v : Fin m → E) :
    (gramPolynomial u v).natDegree ≤ m := by
  have h :=
    Polynomial.natDegree_det_X_add_C_le
      (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v)
      (1 : Matrix (Fin m) (Fin m) ℂ)
  simpa [gramPolynomial, add_comm] using h

/-- Polynomial evaluation recovers the honest shifted determinant
for all complex parameters. -/
theorem gramPolynomial_eval_eq_det {m : ℕ} (u v : Fin m → E)
    (z : ℂ) :
    (gramPolynomial u v).eval z =
      (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det := by
  unfold gramPolynomial
  rw [eval_det, matPolyEquiv_eval_eq_map]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm]

/-- The dimension-free exponential growth estimate at z=1,
proved from the full sharp ℓ¹ polynomial coefficient bound. -/
theorem mixedGram_det_one_add_norm_le_exp {m : ℕ} (u v : Fin m → E) :
    ‖(1 + Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det‖ ≤
      Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  have hdegree : (gramPolynomial u v).natDegree < m + 1 :=
    Nat.lt_succ_of_le (gramPolynomial_natDegree_le u v)
  have hcoeff := gramPolynomial_coeff_l1_le_exp u v
  calc
    ‖(1 + Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det‖ =
      ‖(gramPolynomial u v).eval 1‖ := by
        rw [gramPolynomial_eval_eq_det]
        simp
    _ = ‖∑ k ∈ Finset.range (m + 1), (gramPolynomial u v).coeff k‖ := by
      rw [Polynomial.eval_eq_sum_range' hdegree]
      simp
    _ ≤ ∑ k ∈ Finset.range (m + 1), ‖(gramPolynomial u v).coeff k‖ :=
      norm_sum_le _ _
    _ ≤ Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := hcoeff

/-- For arbitrary complex z, the genuine determinant is an entire
finite-dimensional function with sharp dimension-free growth
‖det(I+zG)‖ ≤ exp(‖z‖ Σ‖uᵢ‖‖vᵢ‖). -/
theorem mixedGram_det_shift_norm_le_exp {m : ℕ}
    (u v : Fin m → E) (z : ℂ) :
    ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det‖ ≤
      Real.exp (‖z‖ * ∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  have hscaled :=
    mixedGram_det_one_add_norm_le_exp
      (fun i : Fin m => z • u i) v
  have hmatrix :
      Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (fun i : Fin m => z • u i) v =
        z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v := by
    ext i j
    simp [Manuscript14Priority3.ComplexGramMinorBridge.mixedGram,
      inner_smul_right, Matrix.smul_apply, smul_eq_mul]
  rw [hmatrix] at hscaled
  convert hscaled using 1
  congr 1
  simp only [norm_smul]
  calc
    ‖z‖ * ∑ i : Fin m, ‖u i‖ * ‖v i‖ =
      ∑ i : Fin m, ‖z‖ * (‖u i‖ * ‖v i‖) := by
        rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ‖z‖ * ‖u i‖ * ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

#print axioms Manuscript14Priority3.FiniteGramEntireGrowth.gramPolynomial_natDegree_le
#print axioms Manuscript14Priority3.FiniteGramEntireGrowth.gramPolynomial_eval_eq_det
#print axioms Manuscript14Priority3.FiniteGramEntireGrowth.mixedGram_det_one_add_norm_le_exp
#print axioms Manuscript14Priority3.FiniteGramEntireGrowth.mixedGram_det_shift_norm_le_exp

end Manuscript14Priority3.FiniteGramEntireGrowth
