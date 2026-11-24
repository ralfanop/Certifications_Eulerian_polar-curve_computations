import Mathlib

/-! M16.6 §13, Fredholm index stability.  The finite-dimensional Schur
block has index equal to the difference of the dimensions of its fixed
domain and codomain, even when its rank changes. The actual affine
operator path is norm-continuous with an exact difference norm.
Unlike shared #458, this does not reprove compact-parametrix preservation.
Index invariance ind(T + K) = ind(T) for an arbitrary Fredholm map T and
compact K is already proved in `SharedCore.FredholmAtkinson.index_add_compact`
(PR #469, in `main`), via local constancy of the index along T + t•K. -/
namespace Manuscript16.V166CompactPerturbationPath

open Module

section FiniteBlock
variable {U V : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]

noncomputable def finiteIndex (A : U →ₗ[ℂ] V) : ℤ :=
  (Module.finrank ℂ A.ker : ℤ) -
    (Module.finrank ℂ (V ⧸ A.range) : ℤ)

/-- Rank-nullity and the quotient dimension formula eliminate rank entirely. -/
theorem finite_block_index (A : U →ₗ[ℂ] V) :
    finiteIndex A = (Module.finrank ℂ U : ℤ) - (Module.finrank ℂ V : ℤ) := by
  have hr := LinearMap.finrank_range_add_finrank_ker A
  have hq := Submodule.finrank_quotient_add_finrank A.range
  unfold finiteIndex
  omega

/-- No continuity, nonsingularity, or constant rank of the finite Schur block
is needed for its index to remain fixed. -/
theorem finite_block_index_independent (A B : U →ₗ[ℂ] V) :
    finiteIndex A = finiteIndex B := by
  rw [finite_block_index, finite_block_index]

theorem finite_endomorphism_index_zero (A : U →ₗ[ℂ] U) :
    finiteIndex A = 0 := by
  rw [finite_block_index, sub_self]

theorem finite_block_family_index_constant {ι : Type*} (A : ι → U →ₗ[ℂ] V)
    (s t : ι) : finiteIndex (A s) = finiteIndex (A t) :=
  finite_block_index_independent _ _

end FiniteBlock

section NormPath
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Exact operator norm of the difference along the affine path. -/
theorem affine_path_difference_norm (T K : E →L[ℂ] F) (s t : ℂ) :
    ‖(T + s • K) - (T + t • K)‖ = ‖s - t‖ * ‖K‖ := by
  have he : (T + s • K) - (T + t • K) = (s - t) • K := by
    rw [sub_smul]
    abel
  rw [he, norm_smul]

theorem compact_homotopy_continuous (T K : E →L[ℂ] F) :
    Continuous (fun t : ℂ => T + t • K) :=
  continuous_const.add (continuous_id.smul continuous_const)

end NormPath
end Manuscript16.V166CompactPerturbationPath

#print axioms Manuscript16.V166CompactPerturbationPath.finite_block_index
#print axioms Manuscript16.V166CompactPerturbationPath.finite_block_index_independent
#print axioms Manuscript16.V166CompactPerturbationPath.finite_endomorphism_index_zero
#print axioms Manuscript16.V166CompactPerturbationPath.finite_block_family_index_constant
#print axioms Manuscript16.V166CompactPerturbationPath.affine_path_difference_norm
#print axioms Manuscript16.V166CompactPerturbationPath.compact_homotopy_continuous
