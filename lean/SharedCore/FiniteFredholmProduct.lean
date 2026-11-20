import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Finite nuclear Fredholm multiplicativity without invertibility

The product (I + UV*)(I + XY*) has a joined nuclear presentation.
Its Gram determinant factors by a product of two block triangular
matrices. No spectral basis, normality or invertibility is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SharedCore.FiniteFredholmProduct
open InnerProductSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def nuclearOp {m : ℕ} (u v : Fin m → E) : E →L[ℂ] E :=
  ∑ k, rankOne ℂ (u k) (v k)

def pairingMatrix {m n : ℕ} (v : Fin m → E) (u : Fin n → E) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => ⟪v i, u j⟫_ℂ

theorem inner_nuclearOp {m : ℕ} (u v : Fin m → E) (w x : E) :
    ⟪w, nuclearOp u v x⟫_ℂ = ∑ k, ⟪w, u k⟫_ℂ * ⟪v k, x⟫_ℂ := by
  simp only [nuclearOp, ContinuousLinearMap.sum_apply, inner_sum, rankOne_apply,
    inner_smul_right]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

theorem triangular_product_det {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin m) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.fromBlocks (1 + A) ((1 + A) * B) C (1 + D + C * B)).det =
      (1 + A).det * (1 + D).det := by
  have h : Matrix.fromBlocks (1 + A) ((1 + A) * B) C (1 + D + C * B) =
      Matrix.fromBlocks (1 + A) 0 C (1 : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) B 0 (1 + D) := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [add_comm (C * B) (1 + D)]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The actual joined nuclear vectors implement the multiplication of
the two identity-plus-finite-rank operators. -/
theorem joined_gram_det {m n : ℕ} (u v : Fin m → E) (x y : Fin n → E) :
    (1 + pairingMatrix (Fin.append v y)
      (Fin.append u (fun j => x j + nuclearOp u v (x j)))).det =
      (1 + pairingMatrix v u).det * (1 + pairingMatrix y x).det := by
  let A := pairingMatrix v u
  let B := pairingMatrix v x
  let C := pairingMatrix y u
  let D := pairingMatrix y x
  have hb : (1 + pairingMatrix (Fin.append v y)
        (Fin.append u (fun j => x j + nuclearOp u v (x j)))).submatrix
        finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (1 + A) ((1 + A) * B) C (1 + D + C * B) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.submatrix, pairingMatrix, Matrix.fromBlocks, Matrix.one_apply, A]
    · simp [Matrix.submatrix, pairingMatrix, Matrix.fromBlocks, Matrix.one_apply, A, B,
        Matrix.add_mul, Matrix.mul_apply, inner_add_right, inner_nuclearOp]
    · simp [Matrix.submatrix, pairingMatrix, Matrix.fromBlocks, Matrix.one_apply, C]
    · simp [Matrix.submatrix, pairingMatrix, Matrix.fromBlocks, Matrix.one_apply, B, C, D,
        Matrix.mul_apply, inner_add_right, inner_nuclearOp, add_assoc]
  calc
    _ = ((1 + pairingMatrix (Fin.append v y)
        (Fin.append u (fun j => x j + nuclearOp u v (x j)))).submatrix
        finSumFinEquiv finSumFinEquiv).det :=
      (Matrix.det_submatrix_equiv_self finSumFinEquiv _).symm
    _ = _ := by rw [hb]; exact triangular_product_det A B C D

#print axioms inner_nuclearOp
#print axioms triangular_product_det
#print axioms joined_gram_det

end SharedCore.FiniteFredholmProduct
