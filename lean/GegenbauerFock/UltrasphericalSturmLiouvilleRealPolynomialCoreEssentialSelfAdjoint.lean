import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosureMaximality

/-!
# V007 — essential self-adjointness of the ORIGINAL polynomial Sturm core

The genuine polynomial-image differential Sturm operator in
weighted real ultraspherical L² admits exactly one self-adjoint
extension. It is its canonical closed graph closure.

This strengthens the closure's self-adjointness to the precise
uniqueness/existence statement on the ORIGINAL polynomial core.
No spectral basis completeness is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every self-adjoint extension of the actual densely defined
polynomial Sturm differential operator equals its canonical closure. -/
theorem sturmRealPolynomialCore_unique_selfAdjoint_extension
    (lam : ℝ) (hlam : 0 < lam)
    (B : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hBself : IsSelfAdjoint B)
    (hAB : sturmRealPartialOperator lam hlam ≤ B) :
    B = (sturmRealPartialOperator lam hlam).closure := by
  let A := sturmRealPartialOperator lam hlam
  have hgraph :
      (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        (B.graph : Set (SturmH lam × SturmH lam)) := by
    intro z hz
    exact (LinearPMap.le_graph_of_le hAB) hz
  have hBclosed : IsClosed (B.graph : Set (SturmH lam × SturmH lam)) :=
    hBself.isClosed
  have hgraphClosure :
      ((A.closure).graph : Set (SturmH lam × SturmH lam)) ⊆
        (B.graph : Set (SturmH lam × SturmH lam)) := by
    rw [← (sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph]
    change closure (A.graph : Set (SturmH lam × SturmH lam)) ⊆ _
    exact closure_minimal hgraph hBclosed
  have hAclosureB : A.closure ≤ B := by
    apply LinearPMap.le_of_le_graph
    intro z hz
    exact hgraphClosure hz
  exact sturmRealClosed_unique_selfAdjoint_extension lam hlam B hAclosureB hBself

/-- The genuine densely defined ultraspherical polynomial Sturm
expression has one and only one self-adjoint extension in real L². -/
theorem sturmRealPolynomialCore_existsUnique_selfAdjoint_extension
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! B : SturmH lam →ₗ.[ℝ] SturmH lam,
      IsSelfAdjoint B ∧ sturmRealPartialOperator lam hlam ≤ B := by
  refine ⟨(sturmRealPartialOperator lam hlam).closure,
    ⟨sturmRealPartialOperator_closure_isSelfAdjoint lam hlam,
      (sturmRealPartialOperator lam hlam).le_closure⟩, ?_⟩
  intro B hB
  exact sturmRealPolynomialCore_unique_selfAdjoint_extension
    lam hlam B hB.1 hB.2

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialCore_unique_selfAdjoint_extension
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialCore_existsUnique_selfAdjoint_extension

end GegenbauerFock.Ultraspherical
