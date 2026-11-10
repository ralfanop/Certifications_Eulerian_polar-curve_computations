import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Manuscript 14.119 Priority 3 — complex mixed-Gram minor expansion

This module works with arbitrary finite families of vectors in a genuine complex
Hilbert space; positivity, normality, and diagonalizability are NOT assumed.

* The mixed Gram entries obey the sharp complex Cauchy–Schwarz bound.
* The complex coefficients of det(I + X G) are exactly sums of principal minors.
* A single (possibly nonselfadjoint) rank-one term has determinant
  1 + z ⟪v,u⟫ and exact first-order norm control.

These statements are formal prerequisites only. The general mixed-Gram
Hadamard inequality for all principal minors, the ensuing uniform perturbation
inequality on genuine CFC S₁(H), and the universal Fredholm extension
are separate, as-yet unproved Lean obligations.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexGramMinorBridge

open Matrix Polynomial
open scoped InnerProductSpace Ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An arbitrary (not necessarily Hermitian) complex mixed Gram pairing. -/
def mixedGram {m : ℕ} (u v : Fin m → E) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => inner ℂ (v i) (u j)

/-- Sharp Cauchy–Schwarz control of every complex mixed-Gram entry. -/
theorem mixedGram_entry_norm_le {m : ℕ} (u v : Fin m → E)
    (i j : Fin m) :
    ‖mixedGram u v i j‖ ≤ ‖v i‖ * ‖u j‖ := by
  exact norm_inner_le_norm (v i) (u j)

/-- Exact principal-minor expansion of the polynomial det(I + X G)
for the arbitrary, potentially nonnormal complex mixed Gram matrix.
The coefficients are sums of ALL k-by-k principal minors. -/
theorem mixedGram_shift_coeff_eq_sum_minors {m : ℕ}
    (u v : Fin m → E) (k : ℕ) :
    (Matrix.det
      (1 + (Polynomial.X : ℂ[X]) • (mixedGram u v).map Polynomial.C)).coeff k =
      ∑ s ∈ Finset.univ.powersetCard k,
        ((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det := by
  exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors (mixedGram u v) k

/-- The actual 1x1 mixed-Gram determinant (complex rank-one base case),
with arbitrary vectors and arbitrary complex spectral parameter. -/
theorem single_mixedGram_shift_det (u v : E) (z : ℂ) :
    (1 + z • mixedGram (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)).det =
      1 + z * inner ℂ v u := by
  rw [Matrix.det_fin_one]
  simp [mixedGram, Matrix.add_apply, Matrix.smul_apply]

/-- Rank-one Fredholm perturbation from the identity: the complex
determinant increment is bounded by the exact rank-one nuclear cost. -/
theorem single_mixedGram_shift_sub_one_norm_le (u v : E) (z : ℂ) :
    ‖(1 + z • mixedGram (fun _ : Fin 1 => u)
        (fun _ : Fin 1 => v)).det - 1‖ ≤ ‖z‖ * ‖u‖ * ‖v‖ := by
  have hCS : ‖inner ℂ v u‖ ≤ ‖v‖ * ‖u‖ :=
    norm_inner_le_norm v u
  calc
    ‖(1 + z • mixedGram (fun _ : Fin 1 => u)
        (fun _ : Fin 1 => v)).det - 1‖ =
        ‖z * inner ℂ v u‖ := by
      rw [single_mixedGram_shift_det]
      congr 1
      ring
    _ = ‖z‖ * ‖inner ℂ v u‖ := norm_mul _ _
    _ ≤ ‖z‖ * (‖v‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left hCS (norm_nonneg z)
    _ = ‖z‖ * ‖u‖ * ‖v‖ := by ring

/-- Dimension-free upper growth bound in the one-term case. -/
theorem single_mixedGram_shift_det_norm_le (u v : E) (z : ℂ) :
    ‖(1 + z • mixedGram (fun _ : Fin 1 => u)
        (fun _ : Fin 1 => v)).det‖ ≤ 1 + ‖z‖ * ‖u‖ * ‖v‖ := by
  have hCS : ‖inner ℂ v u‖ ≤ ‖v‖ * ‖u‖ :=
    norm_inner_le_norm v u
  have hmul : ‖z * inner ℂ v u‖ ≤ ‖z‖ * ‖u‖ * ‖v‖ := by
    calc
      ‖z * inner ℂ v u‖ = ‖z‖ * ‖inner ℂ v u‖ := norm_mul _ _
      _ ≤ ‖z‖ * (‖v‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hCS (norm_nonneg z)
      _ = ‖z‖ * ‖u‖ * ‖v‖ := by ring
  calc
    ‖(1 + z • mixedGram (fun _ : Fin 1 => u)
        (fun _ : Fin 1 => v)).det‖ =
      ‖(1 : ℂ) + z * inner ℂ v u‖ := by rw [single_mixedGram_shift_det]
    _ ≤ ‖(1 : ℂ)‖ + ‖z * inner ℂ v u‖ := norm_add_le _ _
    _ ≤ 1 + ‖z‖ * ‖u‖ * ‖v‖ := by
      simpa only [norm_one, add_comm] using add_le_add_left hmul 1

/-- Unconditional first-order coefficient bound:
the trace term in det(I+XG) is bounded by the exact nuclear
mass of the (possibly nonnormal) finite rank-one family. -/
theorem mixedGram_shift_first_coeff_norm_le_mass {m : ℕ}
    (u v : Fin m → E) :
    ‖(Matrix.det
      (1 + (Polynomial.X : ℂ[X]) • (mixedGram u v).map Polynomial.C)).coeff 1‖ ≤
      ∑ i : Fin m, ‖u i‖ * ‖v i‖ := by
  rw [Matrix.coeff_det_one_add_X_smul_one]
  change ‖∑ i : Fin m, inner ℂ (v i) (u i)‖ ≤
    ∑ i : Fin m, ‖u i‖ * ‖v i‖
  calc
    ‖∑ i : Fin m, inner ℂ (v i) (u i)‖ ≤
        ∑ i : Fin m, ‖inner ℂ (v i) (u i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ‖u i‖ * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_comm] using norm_inner_le_norm (v i) (u i)

/-- EXACT reduction of all complex determinant coefficient estimates
to the missing general mixed-Gram Hadamard bound for principal minors.
The hypothesis hminor is deliberately NOT asserted or assumed as an
axiom; its unconditional proof is the next outstanding obligation. -/
theorem mixedGram_shift_coeff_norm_le_of_minor_control {m : ℕ}
    (u v : Fin m → E) (k : ℕ)
    (hminor : ∀ (s : Finset (Fin m)),
      ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖ ≤
        ∏ i ∈ s, ‖u i‖ * ‖v i‖) :
    ‖(Matrix.det
      (1 + (Polynomial.X : ℂ[X]) • (mixedGram u v).map Polynomial.C)).coeff k‖ ≤
      ∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
  rw [mixedGram_shift_coeff_eq_sum_minors]
  calc
    ‖∑ s ∈ Finset.univ.powersetCard k,
        ((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖ ≤
      ∑ s ∈ Finset.univ.powersetCard k,
        ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro s hs
      exact hminor s

/-- Dimension-independent exponential envelope for the TOTAL mass of
all complex principal minors, CONDITIONAL only on the still-missing
mixed-Gram Hadamard inequality hminor. This precisely reduces the
uniform Fredholm determinant bound to that geometric inequality. -/
theorem mixedGram_total_minor_norm_le_exp_of_minor_control {m : ℕ}
    (u v : Fin m → E)
    (hminor : ∀ (s : Finset (Fin m)),
      ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖ ≤
        ∏ i ∈ s, ‖u i‖ * ‖v i‖) :
    (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
      ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖) ≤
      Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  have hnonneg (i : Fin m) : 0 ≤ ‖u i‖ * ‖v i‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
        ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖) ≤
      ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro s hs
      exact hminor s
    _ = ∏ i : Fin m, (1 + ‖u i‖ * ‖v i‖) := by
      simpa only using
        (Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => ‖u i‖ * ‖v i‖)).symm
    _ ≤ Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
      simpa only using
        (Real.prod_one_add_le_exp_sum (Finset.univ : Finset (Fin m))
          (f := fun i => ‖u i‖ * ‖v i‖) hnonneg)

#print axioms Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_entry_norm_le
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_shift_coeff_eq_sum_minors
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.single_mixedGram_shift_det
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.single_mixedGram_shift_sub_one_norm_le
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.single_mixedGram_shift_det_norm_le
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_shift_first_coeff_norm_le_mass
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_shift_coeff_norm_le_of_minor_control
#print axioms Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_total_minor_norm_le_exp_of_minor_control

end Manuscript14Priority3.ComplexGramMinorBridge
