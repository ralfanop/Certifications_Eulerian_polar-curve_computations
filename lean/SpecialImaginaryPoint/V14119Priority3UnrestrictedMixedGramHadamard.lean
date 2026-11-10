import SpecialImaginaryPoint.V14119Priority3AmbientProjectionSharp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Priority 3 — unrestricted, sharp complex mixed-Gram Hadamard inequality

This module aims to close the geometric obligation of Manuscript 14.119:
  ‖det (⟪vᵢ,uⱼ⟫)‖ ≤ ∏ᵢ ‖uᵢ‖ ‖vᵢ‖
for any finite vector families u,v in any complex inner-product space
E, without assumptions on ambient dimension (even infinite), family
independence, positivity, normality or triangularity.

The independent-u case is proved by orthogonal projection onto span(u)
in the predecessor module. If the determinant is nonzero, columns of
the mixed Gram matrix are independent; since they are images of u under
an actual complex linear map, the u-family is independent.

The sharp estimate passes to EVERY principal minor, and discharges
the previously CONDITIONAL total-minor exponential theorem from PR #101
to an unconditional uniform bound.

The universal S₁(H) determinant, finite-rank perturbation inequality
and holomorphy are still separate proof obligations.
-/

noncomputable section

namespace Manuscript14Priority3.UnrestrictedMixedGramHadamard

open Matrix Polynomial
open scoped Ring
open Manuscript14Priority3.SquareAmbientMixedGramSharp
open Manuscript14Priority3.AmbientProjectionSharp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [Fintype ι] [DecidableEq ι]

/-- A nonzero determinant of a mixed complex Gram matrix forces the
underlying u-family to be complex-linearly independent. This requires
no restriction on ambient Hilbert dimension. -/
theorem mixedGram_det_ne_zero_implies_linearIndependent
    (u v : ι → E)
    (hdet : (squareMixedGram u v).det ≠ 0) :
    LinearIndependent ℂ u := by
  let F : E →ₗ[ℂ] (ι → ℂ) :=
    LinearMap.pi (fun i : ι => (innerSL ℂ (v i)).toLinearMap)
  have hcols : (squareMixedGram u v).col = F ∘ u := by
    funext j i
    simp only [Matrix.col_apply, squareMixedGram, Function.comp_apply,
      F, LinearMap.pi_apply, ContinuousLinearMap.toLinearMap_apply,
      innerSL_apply_apply]
  have hli : LinearIndependent ℂ (F ∘ u) := by
    rw [← hcols]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  exact LinearIndependent.of_comp F hli

/-- The sharp complex mixed-Gram inequality, with constant ONE, for
arbitrary finite families in arbitrary complex inner-product space E.
In particular E may be infinite dimensional. -/
theorem mixedGram_det_norm_le_sharp (u v : ι → E) :
    ‖(squareMixedGram u v).det‖ ≤
      ∏ i : ι, ‖u i‖ * ‖v i‖ := by
  by_cases hu : LinearIndependent ℂ u
  · exact mixedGram_det_norm_le_sharp_of_linearIndependent u v hu
  · have hzero : (squareMixedGram u v).det = 0 := by
      by_contra hz
      exact hu (mixedGram_det_ne_zero_implies_linearIndependent u v hz)
    rw [hzero, norm_zero]
    exact Finset.prod_nonneg fun i hi =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Sharp Gram-Hadamard bound for every complex principal minor,
for arbitrary u and v in arbitrary complex Hilbert ambient dimension.
This discharges the explicit hminor premise from PR #101. -/
theorem mixedGram_principal_minor_norm_le_sharp {m : ℕ}
    (u v : Fin m → E) (s : Finset (Fin m)) :
    ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
      (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ ≤
      ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
  have h : ‖(squareMixedGram (fun i : s => u i)
      (fun i : s => v i)).det‖ ≤
      ∏ i : s, ‖u i‖ * ‖v i‖ :=
    mixedGram_det_norm_le_sharp (fun i : s => u i) (fun i : s => v i)
  have hm :
      squareMixedGram (fun i : s => u i) (fun i : s => v i) =
        (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
          (Subtype.val : s → Fin m) (Subtype.val : s → Fin m) := by
    ext i j
    rfl
  rw [hm] at h
  calc
    ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
      (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖ ≤
        ∏ i : s, ‖u i‖ * ‖v i‖ := h
    _ = ∏ i ∈ s, ‖u i‖ * ‖v i‖ :=
      Finset.prod_coe_sort s (fun i => ‖u i‖ * ‖v i‖)

/-- THE dimension-independent exponential bound for ALL complex
principal minors with no assumptions beyond the complex Hilbert
inner product and finite nuclear vector families.
This is an unconditional instantiation of the PR #101 reduction. -/
theorem mixedGram_total_minor_norm_le_exp_unrestricted {m : ℕ}
    (u v : Fin m → E) :
    (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
      ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
        (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det‖) ≤
      Real.exp (∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  exact Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_total_minor_norm_le_exp_of_minor_control
    u v (fun s => mixedGram_principal_minor_norm_le_sharp u v s)

/-- Every complex Fredholm polynomial coefficient has the
dimension-free sharp k-th elementary symmetric nuclear-mass bound,
without the factorial loss of the unrestricted Leibniz estimate. -/
theorem mixedGram_shift_coeff_norm_le_sharp {m : ℕ}
    (u v : Fin m → E) (k : ℕ) :
    ‖(Matrix.det
      (1 + (Polynomial.X : ℂ[X]) •
        (Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).map
          Polynomial.C)).coeff k‖ ≤
      ∑ s ∈ Finset.univ.powersetCard k,
        ∏ i ∈ s, ‖u i‖ * ‖v i‖ := by
  exact Manuscript14Priority3.ComplexGramMinorBridge.mixedGram_shift_coeff_norm_le_of_minor_control
    u v k (fun s => mixedGram_principal_minor_norm_le_sharp u v s)

#print axioms Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_det_ne_zero_implies_linearIndependent
#print axioms Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_det_norm_le_sharp
#print axioms Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_principal_minor_norm_le_sharp
#print axioms Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_total_minor_norm_le_exp_unrestricted
#print axioms Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_shift_coeff_norm_le_sharp

end Manuscript14Priority3.UnrestrictedMixedGramHadamard
