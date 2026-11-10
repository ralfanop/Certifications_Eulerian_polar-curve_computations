import SpecialImaginaryPoint.V14119Priority3SquareAmbientMixedGramSharp
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Priority 3 — sharp Gram–Hadamard in arbitrary complex Hilbert ambient dimension

The ambient inner-product space E can have arbitrary dimension, including
infinite dimension, and is not required to be complete.

First reduce a linearly independent finite u-family to its m-dimensional
span U. Orthogonally project the v-family onto U; inner products with
u are preserved while the v norm cannot increase. Apply the
kernel-certified square-ambient sharp Gram determinant from PR #104.

The remaining step is handling a linearly dependent u-family
(the mixed Gram determinant is then zero). That statement is NOT
claimed in this module until separately certified.
-/

noncomputable section

namespace Manuscript14Priority3.AmbientProjectionSharp

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [Fintype ι] [DecidableEq ι]

/-- A genuine arbitrary-ambient-dimension sharp complex
mixed-Gram determinant bound, assuming the u-family is linearly
independent but with NO restriction on the v-family or cross pairings. -/
theorem mixedGram_det_norm_le_sharp_of_linearIndependent
    (u v : ι → E) (hu : LinearIndependent ℂ u) :
    ‖(Manuscript14Priority3.SquareAmbientMixedGramSharp.squareMixedGram u v).det‖ ≤
      ∏ i : ι, ‖u i‖ * ‖v i‖ := by
  let U : Submodule ℂ E := Submodule.span ℂ (Set.range u)
  letI : FiniteDimensional ℂ U :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hdim : Module.finrank ℂ U = Fintype.card ι := by
    exact finrank_span_eq_card hu
  letI : CompleteSpace U := FiniteDimensional.complete ℂ U
  letI : U.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace U
  let up : ι → U := fun i => ⟨u i, Submodule.subset_span (Set.mem_range_self i)⟩
  let vp : ι → U := fun i => U.orthogonalProjectionOnto (v i)
  have hgram :
      Manuscript14Priority3.SquareAmbientMixedGramSharp.squareMixedGram u v =
      Manuscript14Priority3.SquareAmbientMixedGramSharp.squareMixedGram up vp := by
    ext i j
    change inner ℂ (v i) (u j) = inner ℂ (vp i) (up j)
    have hinner := U.inner_orthogonalProjectionOnto_eq_of_mem_right
      (up j) (v i)
    simpa only [vp, up] using hinner.symm
  have hproj (i : ι) : ‖vp i‖ ≤ ‖v i‖ := by
    have hop : ‖U.orthogonalProjectionOnto‖ ≤ 1 :=
      U.orthogonalProjectionOnto_norm_le
    calc
      ‖vp i‖ ≤ ‖U.orthogonalProjectionOnto‖ * ‖v i‖ :=
        U.orthogonalProjectionOnto.le_opNorm (v i)
      _ ≤ 1 * ‖v i‖ :=
        mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = ‖v i‖ := one_mul _
  have hmass :
      (∏ i : ι, ‖up i‖ * ‖vp i‖) ≤
        ∏ i : ι, ‖u i‖ * ‖v i‖ := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      calc
        ‖up i‖ * ‖vp i‖ ≤ ‖up i‖ * ‖v i‖ :=
          mul_le_mul_of_nonneg_left (hproj i) (norm_nonneg _)
        _ = ‖u i‖ * ‖v i‖ := by
          rfl
  calc
    ‖(Manuscript14Priority3.SquareAmbientMixedGramSharp.squareMixedGram u v).det‖ =
      ‖(Manuscript14Priority3.SquareAmbientMixedGramSharp.squareMixedGram up vp).det‖ := by
        rw [hgram]
    _ ≤ ∏ i : ι, ‖up i‖ * ‖vp i‖ :=
      Manuscript14Priority3.SquareAmbientMixedGramSharp.mixedGram_det_norm_le_sharp_of_finrank_eq
        hdim up vp
    _ ≤ ∏ i : ι, ‖u i‖ * ‖v i‖ := hmass

#print axioms Manuscript14Priority3.AmbientProjectionSharp.mixedGram_det_norm_le_sharp_of_linearIndependent

end Manuscript14Priority3.AmbientProjectionSharp
