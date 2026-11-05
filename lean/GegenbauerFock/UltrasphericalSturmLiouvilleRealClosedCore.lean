import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosable

/-!
# V007 — certified canonical closure and dense polynomial core

These theorems are consequences of the previously kernel-checked
`IsClosable` result for the genuine real ultraspherical Sturm operator.

We explicitly identify the graph of the canonical closed extension
with the closure of the original graph, show its domain remains dense,
and identify the concrete polynomial-image domain as a graph core.

No essential self-adjointness, equality to the adjoint, or compact
resolvent is claimed.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The graph of the canonical closed Sturm extension is EXACTLY the
topological closure of the original polynomial Sturm graph. -/
theorem sturmRealPartialOperator_closed_graph_eq
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).closure.graph =
      (sturmRealPartialOperator lam hlam).graph.topologicalClosure :=
  (sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph.symm

/-- The original true polynomial partial map is contained in its
canonical closed extension; it is not replaced by a bounded map. -/
theorem sturmRealPartialOperator_le_closed_extension
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPartialOperator lam hlam ≤
      (sturmRealPartialOperator lam hlam).closure :=
  (sturmRealPartialOperator lam hlam).le_closure

/-- The canonical closed extension remains densely defined in the
actual weighted real L² Hilbert space. -/
theorem sturmRealPartialOperator_closure_dense_domain
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).closure.domain.topologicalClosure =
      ⊤ := by
  have hle :
      (sturmRealPartialOperator lam hlam).domain ≤
        (sturmRealPartialOperator lam hlam).closure.domain :=
    (sturmRealPartialOperator_le_closed_extension lam hlam).1
  have hmono := Submodule.topologicalClosure_mono hle
  rw [sturmRealPartialOperator_dense_domain lam hlam] at hmono
  exact top_unique hmono

/-- In the graph norm, the original true polynomial vectors form a
core of the canonical closed extension. -/
theorem sturmRealPartialOperator_closure_polynomial_core
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).closure.HasCore
      (sturmRealPartialOperator lam hlam).domain :=
  (sturmRealPartialOperator lam hlam).closureHasCore

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closed_graph_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_le_closed_extension
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_dense_domain
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_polynomial_core

end GegenbauerFock.Ultraspherical
