import SpecialImaginaryPoint.V14119Priority3ComplexGramMinorBridge
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Priority 3 — Sharp complex mixed-Gram determinant in square ambient dimension

For arbitrary complex vectors uᵢ and vᵢ in a Hilbert space E of complex
dimension n, with n vectors in each family, NO triangularity, positivity,
normality, orthogonality, or linear independence is assumed.

Gram–Schmidt gives a sharp unit-norm bound for the determinant of
any family in any orthonormal basis. A mixed Gram determinant factors
as det(Vᴴ)det(U), yielding the sharp constant 1.

This is an unconditional sharp theorem in a square-ambient sector.
The full arbitrary-ambient-dimension Hilbert-space extension, needed
for the universal CFC S₁(H) determinant, is still a separate obligation.
-/

noncomputable section

namespace Manuscript14Priority3.SquareAmbientMixedGramSharp

open Matrix
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [Fintype ι] [FiniteDimensional ℂ E] [DecidableEq ι]

/-- Gram-Schmidt yields the sharp determinant norm bound in its own
orthonormal basis, even for linearly dependent vector families. -/
theorem gramSchmidt_basis_det_norm_le_prod
    (h : Module.finrank ℂ E = Fintype.card ι)
    (f : ι → E) :
    ‖(InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℂ) h f).toBasis.det f‖ ≤
      ∏ i : ι, ‖f i‖ := by
  let gs := InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℂ) h f
  change ‖gs.toBasis.det f‖ ≤ _
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det]
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    have hcs : ‖inner ℂ (gs i) (f i)‖ ≤ ‖gs i‖ * ‖f i‖ :=
      norm_inner_le_norm _ _
    simpa only [gs.orthonormal.1 i, one_mul] using hcs

/-- Hadamard bound in ANY orthonormal basis, using the unitary
change-of-basis determinant and a Gram–Schmidt basis. -/
theorem orthonormalBasis_det_norm_le_prod
    (h : Module.finrank ℂ E = Fintype.card ι)
    (b : OrthonormalBasis ι ℂ E) (f : ι → E) :
    ‖b.toBasis.det f‖ ≤ ∏ i : ι, ‖f i‖ := by
  let gs := InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℂ) h f
  have hchange :
      b.toBasis.det f = b.toBasis.det gs.toBasis * gs.toBasis.det f := by
    have halt :=
      AlternatingMap.eq_smul_basis_det gs.toBasis (b.toBasis.det)
    have hv := congrArg (fun alt : E [⋀^ι]→ₗ[ℂ] ℂ => alt f) halt
    simpa only [smul_eq_mul, AlternatingMap.smul_apply] using hv
  rw [hchange, norm_mul]
  have hunit : ‖b.toBasis.det gs.toBasis‖ = 1 := by
    exact b.det_to_matrix_orthonormalBasis gs
  rw [hunit, one_mul]
  exact gramSchmidt_basis_det_norm_le_prod h f

/-- The fully arbitrary-index complex mixed Gram matrix in square
Hilbert ambient dimension, with the same orientation as the original
Fin-indexed Priority-3 definition. -/
def squareMixedGram (u v : ι → E) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (v i) (u j)

/-- Mixed Gram matrix coordinate factorization VᴴU in one fixed
orthonormal basis. No normality or positivity assumptions. -/
theorem generalMixedGram_eq_conjTranspose_mul
    (b : OrthonormalBasis ι ℂ E) (u v : ι → E) :
    squareMixedGram u v =
      (b.toBasis.toMatrix v)ᴴ * (b.toBasis.toMatrix u) := by
  ext i j
  simp only [squareMixedGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Module.Basis.toMatrix_apply, b.repr_apply_apply]
  simpa only [b.coe_toBasis_repr_apply, b.repr_apply_apply,
    starRingEnd_apply, inner_conj_symm] using
    (b.sum_inner_mul_inner (v i) (u j)).symm

/-- SHARP Gram–Hadamard bound with constant ONE for arbitrary
complex mixed-Gram matrices G_{ij}=⟪vᵢ,uⱼ⟫, provided the ambient
complex Hilbert dimension equals the size of the families.
The vectors are completely unrestricted. -/
theorem mixedGram_det_norm_le_sharp_of_finrank_eq
    (h : Module.finrank ℂ E = Fintype.card ι)
    (u v : ι → E) :
    ‖(squareMixedGram u v).det‖ ≤
      ∏ i : ι, ‖u i‖ * ‖v i‖ := by
  let b : OrthonormalBasis ι ℂ E :=
    (stdOrthonormalBasis ℂ E).reindex
      (Fintype.equivFinOfCardEq h.symm).symm
  rw [generalMixedGram_eq_conjTranspose_mul b, Matrix.det_mul,
    Matrix.det_conjTranspose, norm_mul, norm_star]
  have hv : ‖(b.toBasis.toMatrix v).det‖ ≤ ∏ i : ι, ‖v i‖ := by
    simpa only [Module.Basis.det_apply] using
      orthonormalBasis_det_norm_le_prod h b v
  have hu : ‖(b.toBasis.toMatrix u).det‖ ≤ ∏ i : ι, ‖u i‖ := by
    simpa only [Module.Basis.det_apply] using
      orthonormalBasis_det_norm_le_prod h b u
  calc
    ‖(b.toBasis.toMatrix v).det‖ * ‖(b.toBasis.toMatrix u).det‖ ≤
      (∏ i : ι, ‖v i‖) * (∏ i : ι, ‖u i‖) :=
      mul_le_mul hv hu (norm_nonneg _) (Finset.prod_nonneg fun i hi => norm_nonneg _)
    _ = ∏ i : ι, ‖u i‖ * ‖v i‖ := by
      rw [Finset.prod_mul_distrib]
      ring

#print axioms Manuscript14Priority3.SquareAmbientMixedGramSharp.gramSchmidt_basis_det_norm_le_prod
#print axioms Manuscript14Priority3.SquareAmbientMixedGramSharp.orthonormalBasis_det_norm_le_prod
#print axioms Manuscript14Priority3.SquareAmbientMixedGramSharp.generalMixedGram_eq_conjTranspose_mul
#print axioms Manuscript14Priority3.SquareAmbientMixedGramSharp.mixedGram_det_norm_le_sharp_of_finrank_eq

end Manuscript14Priority3.SquareAmbientMixedGramSharp
