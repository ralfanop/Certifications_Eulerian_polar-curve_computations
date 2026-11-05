import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedCore
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# V007 — symmetry persists on the genuine closed Sturm graph

The Hilbert Green identity on the dense real polynomial domain extends
to both variables in the closure of the graph, using only continuity
of the real inner product and the already kernel-certified symmetry.

The canonical graph closure is a closed densely-defined *symmetric*
partial real-linear operator on the genuine ultraspherical L² Hilbert
space. This does NOT assert essential self-adjointness (equality to
the adjoint domain) or compactness of the resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The integral Green identity extends in its first graph variable
to the closure, against each original polynomial-domain vector. -/
theorem sturmRealGraphClosure_green_polynomial
    (lam : ℝ) (hlam : 0 < lam)
    (u : SturmH lam × SturmH lam)
    (hu : u ∈ (sturmRealPartialOperator lam hlam).graph.topologicalClosure)
    (y : (sturmRealPartialOperator lam hlam).domain) :
    inner ℝ u.2 (y : SturmH lam) =
      inner ℝ u.1 (sturmRealPartialOperator lam hlam y) := by
  let A := sturmRealPartialOperator lam hlam
  have hcont : Continuous
      (fun w : SturmH lam × SturmH lam =>
        inner ℝ w.2 (y : SturmH lam) -
        inner ℝ w.1 (A y)) := by
    fun_prop
  have hgraph :
      (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ w.2 (y : SturmH lam) -
          inner ℝ w.1 (A y) = 0} := by
    intro w hw
    obtain ⟨x, hx, hy⟩ := (A.mem_graph_iff).mp hw
    have hw_eq : w = ((x : SturmH lam), A x) :=
      Prod.ext hx.symm hy.symm
    rw [hw_eq]
    change inner ℝ (A x) (y : SturmH lam) -
        inner ℝ (x : SturmH lam) (A y) = 0
    rw [sturmRealPartialOperator_symmetric lam hlam x y]
    exact sub_self _
  have hclosure :
      (A.graph.topologicalClosure : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ w.2 (y : SturmH lam) -
          inner ℝ w.1 (A y) = 0} := by
    change closure (A.graph : Set (SturmH lam × SturmH lam)) ⊆ _
    exact closure_minimal hgraph (isClosed_eq hcont continuous_const)
  exact sub_eq_zero.mp (hclosure hu)

/-- The Green identity holds for arbitrary PAIRS of vectors in the
true closed graph of the densely-defined Sturm partial operator. -/
theorem sturmRealGraphClosure_green
    (lam : ℝ) (hlam : 0 < lam)
    (u v : SturmH lam × SturmH lam)
    (hu : u ∈ (sturmRealPartialOperator lam hlam).graph.topologicalClosure)
    (hv : v ∈ (sturmRealPartialOperator lam hlam).graph.topologicalClosure) :
    inner ℝ u.2 v.1 = inner ℝ u.1 v.2 := by
  let A := sturmRealPartialOperator lam hlam
  have hcont : Continuous
      (fun w : SturmH lam × SturmH lam =>
        inner ℝ u.2 w.1 - inner ℝ u.1 w.2) := by
    fun_prop
  have hgraph :
      (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ u.2 w.1 -
          inner ℝ u.1 w.2 = 0} := by
    intro w hw
    obtain ⟨y, hy1, hy2⟩ := (A.mem_graph_iff).mp hw
    have hw_eq : w = ((y : SturmH lam), A y) :=
      Prod.ext hy1.symm hy2.symm
    rw [hw_eq]
    exact sub_eq_zero.mpr
      (sturmRealGraphClosure_green_polynomial lam hlam u hu y)
  have hclosure :
      (A.graph.topologicalClosure : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ u.2 w.1 -
          inner ℝ u.1 w.2 = 0} := by
    change closure (A.graph : Set (SturmH lam × SturmH lam)) ⊆ _
    exact closure_minimal hgraph (isClosed_eq hcont continuous_const)
  exact sub_eq_zero.mp (hclosure hv)

/-- The canonical closed unbounded real Sturm operator is symmetric
on its full actual closed graph, not merely on original polynomials. -/
theorem sturmRealPartialOperator_closure_symmetric
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain) :
    inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
      (y : SturmH lam) =
    inner ℝ (x : SturmH lam)
      ((sturmRealPartialOperator lam hlam).closure y) := by
  have hx : ((x : SturmH lam),
      (sturmRealPartialOperator lam hlam).closure x) ∈
      (sturmRealPartialOperator lam hlam).graph.topologicalClosure := by
    rw [(sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph]
    exact (sturmRealPartialOperator lam hlam).closure.mem_graph x
  have hy : ((y : SturmH lam),
      (sturmRealPartialOperator lam hlam).closure y) ∈
      (sturmRealPartialOperator lam hlam).graph.topologicalClosure := by
    rw [(sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph]
    exact (sturmRealPartialOperator lam hlam).closure.mem_graph y
  exact sturmRealGraphClosure_green lam hlam _ _ hx hy

#print axioms GegenbauerFock.Ultraspherical.sturmRealGraphClosure_green_polynomial
#print axioms GegenbauerFock.Ultraspherical.sturmRealGraphClosure_green
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_symmetric

end GegenbauerFock.Ultraspherical
