import GegenbauerFock.UltrasphericalSturmLiouvilleRealPMapClosure

/-!
# V007 — precise graph closure and polynomial core for real Sturm L²

This module identifies the graph of the canonical closed extension of
the genuine real ultraspherical polynomial-domain differential
operator with the closure of its graph in the product Hilbert space.

The Mathlib graph-core property shows that the original polynomial
domain is a core of this operator's canonical graph closure.

This is a graph-theoretic closure, not essential self-adjointness or a
spectral assertion.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The graph of the closed extension is exactly the closure of the
true polynomial Sturm operator's graph. -/
theorem sturmRealPMap_graph_closure_eq
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).graph.topologicalClosure =
      (sturmRealPMap lam hlam).closure.graph :=
  (sturmRealPMap_isClosable lam hlam).graph_closure_eq_closure_graph

/-- Original real ultraspherical polynomials remain a graph core
of the canonical closed extension of the dense symmetric operator. -/
theorem sturmRealPMap_polynomials_core
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).closure.HasCore
      (sturmRealPMap lam hlam).domain :=
  LinearPMap.closureHasCore (sturmRealPMap lam hlam)

/-- The canonical closed extension is itself closable. -/
theorem sturmRealPMap_closure_isClosable
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).closure.IsClosable :=
  (sturmRealPMap_closure_isClosed lam hlam).isClosable

#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_graph_closure_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_polynomials_core
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_closure_isClosable

end GegenbauerFock.Ultraspherical
