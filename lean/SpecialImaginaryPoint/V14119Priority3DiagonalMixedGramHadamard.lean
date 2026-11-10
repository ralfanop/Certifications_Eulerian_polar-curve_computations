import SpecialImaginaryPoint.V14119Priority3ComplexGramMinorBridge

/-!
# Priority 3: genuine all-order mixed-Gram Hadamard inequality in diagonal sector

The complex mixed Gram matrix G_{ij}=⟪v_i,u_j⟫ can be non-Hermitian.
If its off-diagonal pairings vanish, every principal minor has the
sharp determinant bound by its nuclear costs. This handles arbitrary
finite index dimensions and all principal minors, not just rank one.
No positivity assumption on the diagonal pairings is used.

The unrestricted mixed-Gram Hadamard inequality (off-diagonal
pairings allowed) remains a separate open formalization obligation.
-/

noncomputable section

namespace Manuscript14Priority3.DiagonalMixedGramHadamard

open Matrix
open scoped InnerProductSpace
open Manuscript14Priority3.ComplexGramMinorBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An arbitrary complex mixed-Gram matrix whose off-diagonal
pairings vanish is precisely its (potentially non-Hermitian) diagonal. -/
theorem mixedGram_eq_diagonal_of_offdiag_zero {m : ℕ}
    (u v : Fin m → E)
    (hzero : ∀ i j : Fin m, i ≠ j → inner ℂ (v i) (u j) = 0) :
    mixedGram u v = Matrix.diagonal (fun i => inner ℂ (v i) (u i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [mixedGram]
  · simp [mixedGram, hij, hzero i j hij]

/-- Sharp all-order complex Hadamard inequality when the mixed
pairings are off-diagonally zero. The diagonal entries can be
arbitrary complex numbers and the Hilbert space dimension is free. -/
theorem mixedGram_det_norm_le_cost_of_offdiag_zero {m : ℕ}
    (u v : Fin m → E)
    (hzero : ∀ i j : Fin m, i ≠ j → inner ℂ (v i) (u j) = 0) :
    ‖(mixedGram u v).det‖ ≤ ∏ i : Fin m, ‖u i‖ * ‖v i‖ := by
  rw [mixedGram_eq_diagonal_of_offdiag_zero u v hzero,
    Matrix.det_diagonal, norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa only [mul_comm] using norm_inner_le_norm (v i) (u i)

/-- Every complex principal minor, for ANY finite subset of indices,
satisfies the SHARP mixed-Gram Hadamard inequality in the
off-diagonally-zero sector. -/
theorem mixedGram_minor_norm_le_cost_of_offdiag_zero {m : ℕ}
    (u v : Fin m → E)
    (hzero : ∀ i j : Fin m, i ≠ j → inner ℂ (v i) (u j) = 0)
    (s : Finset (Fin m)) :
    ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖ ≤
      ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
  let us : s → E := fun i => u i
  let vs : s → E := fun i => v i
  have hs :
      ((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)) =
        Matrix.diagonal (fun i : s => inner ℂ (v i) (u i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [mixedGram]
    · have hcoe : (i : Fin m) ≠ (j : Fin m) := by
        intro h
        exact hij (Subtype.ext h)
      simp [mixedGram, hij, hzero i j hcoe]
  rw [hs, Matrix.det_diagonal, norm_prod]
  calc
    (∏ i : s, ‖inner ℂ (v i) (u i)‖) ≤
      ∏ i : s, ‖u i‖ * ‖v i‖ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          simpa only [mul_comm] using norm_inner_le_norm (v i) (u i)
    _ = ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
      exact Finset.prod_attach s (fun i => ‖u i‖ * ‖v i‖)

/-- Discharge the exact Hadamard prerequisite of the previous
complex-Gram coefficient theorem in the diagonal (not necessarily
positive) sector, for arbitrary finite size and all k. -/
theorem mixedGram_shift_coeff_norm_le_diagonal {m : ℕ}
    (u v : Fin m → E)
    (hzero : ∀ i j : Fin m, i ≠ j → inner ℂ (v i) (u j) = 0)
    (k : ℕ) :
    ‖(Matrix.det
      (1 + (Polynomial.X : ℂ[X]) • (mixedGram u v).map Polynomial.C)).coeff k‖ ≤
      ∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
  exact mixedGram_shift_coeff_norm_le_of_minor_control u v k
    (mixedGram_minor_norm_le_cost_of_offdiag_zero u v hzero)

/-- Unconditional all-minors exponential mass bound in the diagonal
complex sector; independent of the finite dimension. -/
theorem mixedGram_total_minor_norm_le_exp_diagonal {m : ℕ}
    (u v : Fin m → E)
    (hzero : ∀ i j : Fin m, i ≠ j → inner ℂ (v i) (u j) = 0) :
    (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
      ‖((mixedGram u v).submatrix (Subtype.val : s → Fin m)
          (Subtype.val : s → Fin m)).det‖) ≤
      Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  exact mixedGram_total_minor_norm_le_exp_of_minor_control u v
    (mixedGram_minor_norm_le_cost_of_offdiag_zero u v hzero)

#print axioms Manuscript14Priority3.DiagonalMixedGramHadamard.mixedGram_eq_diagonal_of_offdiag_zero
#print axioms Manuscript14Priority3.DiagonalMixedGramHadamard.mixedGram_det_norm_le_cost_of_offdiag_zero
#print axioms Manuscript14Priority3.DiagonalMixedGramHadamard.mixedGram_minor_norm_le_cost_of_offdiag_zero
#print axioms Manuscript14Priority3.DiagonalMixedGramHadamard.mixedGram_shift_coeff_norm_le_diagonal
#print axioms Manuscript14Priority3.DiagonalMixedGramHadamard.mixedGram_total_minor_norm_le_exp_diagonal

end Manuscript14Priority3.DiagonalMixedGramHadamard
