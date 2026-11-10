import SpecialImaginaryPoint.V14119Priority3UnrestrictedMixedGramHadamard

/-!
# Priority 3 — sharp ℓ¹ coefficients of unrestricted complex Fredholm polynomials

The unrestricted sharp Gram–Hadamard certificate (#107) immediately
bounds EACH Fredholm polynomial coefficient by the elementary-symmetric
nuclear cost. This module adds the exact combinatorial sum across
degrees, certifying a dimension-independent bound on the complete
ℓ¹ coefficient mass:

 Σ_{k=0}^m |[X^k] det(I+XG)| ≤ exp(Σ_i ‖u_i‖‖v_i‖).

No positivity, normality, triangularity, vector-family independence or
ambient Hilbert-dimension restriction is assumed.

This is the complex-polynomial coefficient bridge for the subsequent
pointwise determinant bound and trace-norm perturbation theorem; it does
not yet construct the infinite-dimensional Fredholm determinant.
-/

noncomputable section

namespace Manuscript14Priority3.SharpPolynomialMass

open Matrix Polynomial
open scoped InnerProductSpace Ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite intrinsic complex Fredholm determinant polynomial of an
arbitrary mixed-Gram rank-one family. -/
def gramPolynomial {m : ℕ} (u v : Fin m → E) : ℂ[X] :=
  Matrix.det (1 + (Polynomial.X : ℂ[X]) •
    (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).map Polynomial.C)

/-- Sharp total polynomial coefficient mass. No factorial loss, no
dimension dependence, no Gram positivity and no operator diagonalization. -/
theorem gramPolynomial_coeff_l1_le_exp {m : ℕ} (u v : Fin m → E) :
    (∑ k ∈ Finset.range (m + 1), ‖(gramPolynomial u v).coeff k‖) ≤
      Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  have hcoeff (k : ℕ) :
      ‖(gramPolynomial u v).coeff k‖ ≤
        ∑ s ∈ Finset.univ.powersetCard k,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
    exact Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_shift_coeff_norm_le_sharp u v k
  have hmass :=
    Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_total_minor_norm_le_exp_unrestricted u v
  have hsym :
      (∑ k ∈ Finset.range (m + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖) =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
    rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
    simp
  have hgeom :
      (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖) ≤
        Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
    have hnonneg (i : Fin m) : 0 ≤ ‖u i‖ * ‖v i‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖) =
        ∏ i : Fin m, (1 + ‖u i‖ * ‖v i‖) := by
          simpa only using
            (Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
              (f := fun i => ‖u i‖ * ‖v i‖)).symm
      _ ≤ Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
        simpa only using
          (Real.prod_one_add_le_exp_sum (Finset.univ : Finset (Fin m)) hnonneg)
  calc
    (∑ k ∈ Finset.range (m + 1), ‖(gramPolynomial u v).coeff k‖) ≤
      (∑ k ∈ Finset.range (m + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hcoeff k
    _ = ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∏ i ∈ s, ‖u i‖ * ‖v i‖ := hsym
    _ ≤ Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := hgeom

#print axioms Manuscript14Priority3.SharpPolynomialMass.gramPolynomial_coeff_l1_le_exp

end Manuscript14Priority3.SharpPolynomialMass
