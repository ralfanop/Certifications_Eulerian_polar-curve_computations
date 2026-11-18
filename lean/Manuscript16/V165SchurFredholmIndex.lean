import Manuscript16.V165SchurClosedRange
import Manuscript16.V165SchurKernelReduction

/-! M16 v16.5 §13. Genuine algebraic kernel and cokernel equivalences
for the typed graph block, closed-range transfer and Fredholm index.
The continuous linear inverse L:D ≃L X remains an explicit hypothesis.
No compact perturbation or concrete graph-domain realization is assumed. -/
namespace Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Graph of the forced second component over the actual Schur kernel. -/
def kernelEquiv (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    LinearMap.ker (block A B C L).toLinearMap ≃ₗ[𝕜]
    LinearMap.ker (schur A B C L).toLinearMap where
  toFun z := ⟨z.val.1, ((block_kernel_iff A B C L z.val.1 z.val.2).1 z.property).1⟩
  invFun p := ⟨(p.val, -L.symm (C p.val)), schur_kernel_lift A B C L p.val p.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((block_kernel_iff A B C L z.val.1 z.val.2).1 z.property).2.symm
  right_inv p := by
    apply Subtype.ext
    rfl
  map_add' z w := by
    apply Subtype.ext
    rfl
  map_smul' c z := by
    apply Subtype.ext
    rfl

/-- Codomain shear followed by projection to the resonant component. -/
def cokernelProjection (B : D →L[𝕜] P) (L : D ≃L[𝕜] X) :
    (P × X) →ₗ[𝕜] P where
  toFun z := z.1 - B (L.symm z.2)
  map_add' := by
    rintro ⟨f,g⟩ ⟨f',g'⟩
    change f + f' - B (L.symm (g + g')) =
      (f - B (L.symm g)) + (f' - B (L.symm g'))
    simp only [map_add]
    abel
  map_smul' := by
    rintro c ⟨f,g⟩
    change c • f - B (L.symm (c • g)) = c • (f - B (L.symm g))
    simp [smul_sub]

theorem cokernelProjection_surjective (B : D →L[𝕜] P) (L : D ≃L[𝕜] X) :
    Function.Surjective (cokernelProjection B L) := by
  intro f
  refine ⟨(f,0),?_⟩
  change f - B (L.symm 0) = f
  simp

def cokernelMap (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    (P × X) →ₗ[𝕜] (P ⧸ LinearMap.range (schur A B C L).toLinearMap) :=
  (LinearMap.range (schur A B C L).toLinearMap).mkQ.comp (cokernelProjection B L)

theorem cokernelMap_ker (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    LinearMap.ker (cokernelMap A B C L) = LinearMap.range (block A B C L).toLinearMap := by
  ext z
  rcases z with ⟨f,g⟩
  change ((LinearMap.range (schur A B C L).toLinearMap).mkQ
    (f - B (L.symm g)) = 0) ↔ (f,g) ∈ Set.range (block A B C L)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_block_range_iff A B C L f g).symm

theorem cokernelMap_surjective (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    Function.Surjective (cokernelMap A B C L) :=
  (Submodule.mkQ_surjective _).comp (cokernelProjection_surjective B L)

/-- Actual quotient spaces, not just a numerical equality of dimensions. -/
noncomputable def cokernelEquiv (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    ((P × X) ⧸ LinearMap.range (block A B C L).toLinearMap) ≃ₗ[𝕜]
    (P ⧸ LinearMap.range (schur A B C L).toLinearMap) :=
  (Submodule.quotEquivOfEq _ _ (cokernelMap_ker A B C L).symm).trans
    (LinearMap.quotKerEquivOfSurjective (cokernelMap A B C L)
      (cokernelMap_surjective A B C L))

private theorem finite_equiv_iff {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (e : M ≃ₗ[𝕜] N) :
    Module.Finite 𝕜 M ↔ Module.Finite 𝕜 N := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · intro h
    letI := h
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The usual three defining properties of a Fredholm bounded map,
explicitly recorded for a normed graph-domain realization. -/
def HasFredholmData {M N : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] (T : M →L[𝕜] N) : Prop :=
  IsClosed (Set.range T) ∧ Module.Finite 𝕜 (LinearMap.ker T.toLinearMap) ∧
    Module.Finite 𝕜 (N ⧸ LinearMap.range T.toLinearMap)

theorem block_fredholm_data_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    HasFredholmData (block A B C L) ↔ HasFredholmData (schur A B C L) :=
  and_congr (block_range_closed_iff A B C L)
    (and_congr (finite_equiv_iff (kernelEquiv A B C L))
      (finite_equiv_iff (cokernelEquiv A B C L)))

/-- Integer index is nullity minus defect, interpreted as a Fredholm
index when HasFredholmData holds. -/
noncomputable def fredholmIndex {M N : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] (T : M →L[𝕜] N) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker T.toLinearMap) : ℤ) -
    (Module.finrank 𝕜 (N ⧸ LinearMap.range T.toLinearMap) : ℤ)

theorem block_fredholm_index_eq (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    fredholmIndex (block A B C L) = fredholmIndex (schur A B C L) := by
  unfold fredholmIndex
  rw [(kernelEquiv A B C L).finrank_eq, (cokernelEquiv A B C L).finrank_eq]

#print axioms Manuscript16.V165GraphSchur.kernelEquiv
#print axioms Manuscript16.V165GraphSchur.cokernelMap_ker
#print axioms Manuscript16.V165GraphSchur.cokernelMap_surjective
#print axioms Manuscript16.V165GraphSchur.cokernelEquiv
#print axioms Manuscript16.V165GraphSchur.block_fredholm_data_iff
#print axioms Manuscript16.V165GraphSchur.block_fredholm_index_eq
end Manuscript16.V165GraphSchur
