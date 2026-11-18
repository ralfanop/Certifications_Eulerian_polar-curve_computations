import Manuscript16.V165TypedGraphSchur

/-!
M16 v16.5 §13: exact kernel reduction of the typed Schur block.
This is conditional on the explicit continuous linear equivalence L : D ≃L X.
No assertion of Fredholmness, compactness, index or det4 is made.
-/
namespace Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The full block kernel is the graph of -L⁻¹C over the Schur kernel. -/
theorem block_kernel_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) (p : P) (x : D) :
    block A B C L (p,x) = 0 ↔
      schur A B C L p = 0 ∧ x = -L.symm (C p) := by
  have h := block_equation_iff A B C L p 0 x 0
  change block A B C L (p, x) = (0, 0) ↔
    schur A B C L p = 0 ∧ x = -L.symm (C p)
  simpa using h

/-- Every Schur null vector gives a block null vector. -/
theorem schur_kernel_lift (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) (p : P)
    (hp : schur A B C L p = 0) :
    block A B C L (p, -L.symm (C p)) = 0 := by
  exact (block_kernel_iff A B C L p (-L.symm (C p))).2 ⟨hp, rfl⟩

#print axioms Manuscript16.V165GraphSchur.block_kernel_iff
#print axioms Manuscript16.V165GraphSchur.schur_kernel_lift
end Manuscript16.V165GraphSchur
