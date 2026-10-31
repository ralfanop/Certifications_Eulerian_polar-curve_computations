import GegenbauerFock.UltrasphericalSturmLiouvilleRealPartialOperator
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# V007 — closability of the genuine ultraspherical Sturm polynomial operator

We show that the graph closure of the actual densely defined symmetric
real L²(νλ) Sturm operator contains no nonzero vertical vector. The
proof uses continuity of the real Hilbert inner product, the already
certified Green symmetry on the genuine polynomial domain and the
independently certified density of that domain.

This produces a genuine `LinearPMap.IsClosable` theorem and hence a
well-defined closed graph extension. It does NOT claim essential
self-adjointness, equality of adjoint domains, or compact resolvent.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual dense real polynomial domain as a dense subset of L². -/
theorem sturmRealPolynomialDomain_dense_set
    (lam : ℝ) (hlam : 0 < lam) :
    Dense (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) := by
  rw [dense_iff_closure_eq]
  have hc :
      closure (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) =
        ((sturmRealPolynomialDomain lam hlam).topologicalClosure :
          Set (SturmH lam)) := rfl
  rw [hc, sturmRealPolynomialDomain_dense lam hlam]
  rfl

/-- A point in the closure of the genuine Sturm graph whose first
coordinate is zero has second coordinate zero, by Green symmetry and
the dense-domain uniqueness of inner-product pairings. -/
theorem sturmRealPartialOperator_graph_vertical_zero
    (lam : ℝ) (hlam : 0 < lam)
    (w : SturmH lam × SturmH lam)
    (hw : w ∈ (sturmRealPartialOperator lam hlam).graph.topologicalClosure)
    (hw0 : w.1 = 0) : w.2 = 0 := by
  let A := sturmRealPartialOperator lam hlam
  have hdense := sturmRealPolynomialDomain_dense_set lam hlam
  apply hdense.eq_zero_of_inner_left ℝ
  intro v hv
  let z : sturmRealPolynomialDomain lam hlam := ⟨v, hv⟩
  have hcont : Continuous (fun u : SturmH lam × SturmH lam =>
      inner ℝ u.2 v - inner ℝ u.1 (A z)) := by
    fun_prop
  have hclosed : IsClosed
      {u : SturmH lam × SturmH lam |
        inner ℝ u.2 v - inner ℝ u.1 (A z) = 0} :=
    isClosed_eq hcont continuous_const
  have hgraph :
      (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        {u | inner ℝ u.2 v - inner ℝ u.1 (A z) = 0} := by
    intro u hu
    obtain ⟨x, hx, hy⟩ := (A.mem_graph_iff).mp hu
    have hu_eq : u = ((x : SturmH lam), A x) :=
      Prod.ext hx.symm hy.symm
    rw [hu_eq]
    change inner ℝ (A x) (z : SturmH lam) -
        inner ℝ (x : SturmH lam) (A z) = 0
    rw [sturmRealPartialOperator_symmetric lam hlam x z]
    exact sub_self _
  have hclosure :
      (A.graph.topologicalClosure : Set (SturmH lam × SturmH lam)) ⊆
        {u | inner ℝ u.2 v - inner ℝ u.1 (A z) = 0} := by
    change closure (A.graph : Set (SturmH lam × SturmH lam)) ⊆ _
    exact closure_minimal hgraph hclosed
  have horth : inner ℝ w.2 v - inner ℝ w.1 (A z) = 0 :=
    hclosure (show w ∈ A.graph.topologicalClosure from hw)
  simpa [hw0] using horth

/-- The real ultraspherical Sturm differential expression on its
true polynomial-image L²-domain is a closable partial linear operator.
No operator-boundedness or boundary conditions are assumed. -/
theorem sturmRealPartialOperator_isClosable
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).IsClosable := by
  let A := sturmRealPartialOperator lam hlam
  have hvertical :
      ∀ (w : SturmH lam × SturmH lam)
        (_hw : w ∈ A.graph.topologicalClosure) (_hz : w.1 = 0),
        w.2 = 0 := by
    intro w hw hz
    exact sturmRealPartialOperator_graph_vertical_zero lam hlam w hw hz
  refine ⟨A.graph.topologicalClosure.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq
    A.graph.topologicalClosure hvertical).symm

/-- Its canonical graph closure in the Mathlib partial-operator API is
a closed extension of the actual real polynomial Sturm expression. -/
theorem sturmRealPartialOperator_closure_isClosed
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).closure.IsClosed :=
  (sturmRealPartialOperator_isClosable lam hlam).closure_isClosed

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialDomain_dense_set
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_graph_vertical_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_isClosable
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_isClosed

end GegenbauerFock.Ultraspherical
