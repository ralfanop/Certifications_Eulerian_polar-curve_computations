import SpecialImaginaryPoint.V14119Priority3ComplexGramMinorBridge

/-!
# Priority 3 — unconditional mixed complex Gram determinant (Leibniz) bound

For arbitrary complex Hilbert vectors, WITHOUT zero off-diagonal, normality
or self-adjointness assumptions, the Leibniz expansion and the
Cauchy–Schwarz inequality give:

  ‖det(⟪vᵢ,uⱼ⟫)‖ ≤ n! * ∏ᵢ ‖uᵢ‖ ‖vᵢ‖.

The same estimate holds for every principal minor of an arbitrary
mixed-Gram matrix, with the factorial of that minor's size.

WARNING: The factorial is a genuine loss of the naive permutation-sum
argument. This does NOT discharge the sharp Gram–Hadamard premise needed
for the dimension-INDEPENDENT Fredholm determinant estimates. The goal
remains to remove the factorial using Hilbert-space exterior products,
Gram–Schmidt, or another valid method, without adding new axioms.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexGramLeibnizBound

open Matrix Polynomial
open scoped InnerProductSpace Ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Mixed complex Gram matrix for an arbitrary finite type, not just Fin m. -/
def generalMixedGram {ι : Type*} (u v : ι → E) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (v i) (u j)

/-- General all-order mixed-complex-Gram determinant bound from
Leibniz permutations and Cauchy–Schwarz. It has the unavoidable
n! loss of this proof strategy and is NOT the sharp Hadamard bound. -/
theorem generalMixedGram_det_norm_le_factorial_cost
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → E) :
    ‖(generalMixedGram u v).det‖ ≤
      ((Nat.factorial (Fintype.card ι)) : ℝ) *
        (∏ i : ι, ‖u i‖ * ‖v i‖) := by
  rw [Matrix.det_apply]
  calc
    ‖∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ • ∏ i : ι, generalMixedGram u v (σ i) i‖ ≤
        ∑ σ : Equiv.Perm ι,
          ‖Equiv.Perm.sign σ • ∏ i : ι, generalMixedGram u v (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι,
          ∏ i : ι, ‖generalMixedGram u v (σ i) i‖ := by
      simp only [norm_units_zsmul, norm_prod]
    _ ≤ ∑ σ : Equiv.Perm ι,
          ∏ i : ι, ‖v (σ i)‖ * ‖u i‖ := by
      apply Finset.sum_le_sum
      intro σ hσ
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        change ‖inner ℂ (v (σ i)) (u i)‖ ≤ ‖v (σ i)‖ * ‖u i‖
        exact norm_inner_le_norm _ _
    _ = ∑ σ : Equiv.Perm ι,
          (∏ i : ι, ‖v i‖) * (∏ i : ι, ‖u i‖) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      exact congrArg (fun x : ℝ => x * ∏ i : ι, ‖u i‖)
        (Equiv.prod_comp σ (fun i : ι => ‖v i‖))
    _ = ((Nat.factorial (Fintype.card ι)) : ℝ) *
          ((∏ i : ι, ‖v i‖) * (∏ i : ι, ‖u i‖)) := by
      simp [Fintype.card_perm, nsmul_eq_mul]
    _ = ((Nat.factorial (Fintype.card ι)) : ℝ) *
          (∏ i : ι, ‖u i‖ * ‖v i‖) := by
      rw [Finset.prod_mul_distrib]
      ring

/-- All principal minors of an unrestricted complex mixed Gram matrix
obey the Leibniz factorial-cost bound with factorial (card s)!.
Unlike the sharp Hadamard inequality, this is not dimension-uniform. -/
theorem mixedGram_principal_minor_norm_le_factorial_cost
    {m : ℕ} (u v : Fin m → E) (s : Finset (Fin m)) :
    ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
      (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ ≤
        ((Nat.factorial s.card) : ℝ) * (∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
  have h := generalMixedGram_det_norm_le_factorial_cost
    (u := fun i : s => u i) (v := fun i : s => v i)
  have hm :
      generalMixedGram (fun i : s => u i) (fun i : s => v i) =
        (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m) := by
    ext i j
    rfl
  rw [hm] at h
  calc
    ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
      (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ ≤
        ((Nat.factorial s.card) : ℝ) *
          (∏ i : s, ‖u i‖ * ‖v i‖) := by
      simpa only [Fintype.card_coe] using h
    _ = ((Nat.factorial s.card) : ℝ) *
          (∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
      exact congrArg
        (fun r : ℝ => ((Nat.factorial s.card) : ℝ) * r)
        (Finset.prod_coe_sort s (fun i => ‖u i‖ * ‖v i‖))

/-- Every coefficient of det(I+XG), with fully arbitrary nonnormal
complex mixed Gram entries, has an unconditional k!-weighted
elementary-symmetric nuclear-cost bound. This is weaker than the
sharp Hadamard coefficient estimate by the factor k!. -/
theorem mixedGram_shift_coeff_norm_le_factorial_cost
    {m : ℕ} (u v : Fin m → E) (k : ℕ) :
    ‖(Matrix.det
      (1 + (Polynomial.X : ℂ[X]) •
        (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).map
          Polynomial.C)).coeff k‖ ≤
      ((Nat.factorial k) : ℝ) *
      (∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
  rw [Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_shift_coeff_eq_sum_minors]
  calc
    ‖∑ s ∈ Finset.univ.powersetCard k,
        ((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ ≤
      ∑ s ∈ Finset.univ.powersetCard k,
        ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.univ.powersetCard k,
        ((Nat.factorial k) : ℝ) * (∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
      apply Finset.sum_le_sum
      intro s hs
      have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
      simpa only [hcard] using
        mixedGram_principal_minor_norm_le_factorial_cost u v s
    _ = ((Nat.factorial k) : ℝ) *
      (∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
      rw [Finset.mul_sum]

#print axioms Manuscript14Priority3.ComplexGramLeibnizBound.generalMixedGram_det_norm_le_factorial_cost
#print axioms Manuscript14Priority3.ComplexGramLeibnizBound.mixedGram_principal_minor_norm_le_factorial_cost
#print axioms Manuscript14Priority3.ComplexGramLeibnizBound.mixedGram_shift_coeff_norm_le_factorial_cost

end Manuscript14Priority3.ComplexGramLeibnizBound
