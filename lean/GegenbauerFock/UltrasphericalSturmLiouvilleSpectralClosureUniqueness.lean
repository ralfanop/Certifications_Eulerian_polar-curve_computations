import GegenbauerFock.UltrasphericalSturmLiouvilleRealShiftDenseRange
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# V007 — uniqueness of the closed spectral Sturm realization

This is a *reverse inclusion* theorem, not merely a closed-extension result.
It uses the already certified dense image of I - L on actual weighted-L²
polynomial vectors.

For a candidate closed spectral realization S extending the genuine
polynomial differential operator, an explicit quantitative estimate on
its shifted graph implies that EVERY S-graph point is approximated
simultaneously in its input and output coordinates by polynomial
graph points. Thus S is exactly the canonical graph closure.

The spectral graph estimate is deliberately an explicit hypothesis:
a concrete diagonal spectral model must establish it (for example from
its nonpositive real spectrum). This module alone does NOT construct
that diagonal model or prove essential self-adjointness.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A closed extension with a quantitatively controlled shifted graph
is not merely an extension: it is EXACTLY the closure of the genuine
polynomial Sturm operator. The density of the shifted polynomial range
is a theorem of the V007 repository, not an extra hypothesis. -/
theorem sturmRealPartialOperator_spectral_eq_closure_of_shift_graph_bound
    (lam : ℝ) (hlam : 0 < lam)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hSclosed : S.IsClosed)
    (hExt : sturmRealPartialOperator lam hlam ≤ S)
    (hGraphBound : ∀ x y : S.domain,
      dist (((x : SturmH lam), S x) : SturmH lam × SturmH lam)
           (((y : SturmH lam), S y) : SturmH lam × SturmH lam) ≤
        3 * dist ((x : SturmH lam) - S x)
                 ((y : SturmH lam) - S y)) :
    (sturmRealPartialOperator lam hlam).closure = S := by
  let A := sturmRealPartialOperator lam hlam
  have hDense : DenseRange (fun x : A.domain =>
      (x : SturmH lam) - A x) :=
    sturmRealPartialShift_denseRange lam hlam
  have hGraphRange :
      Set.range (fun x : A.domain =>
          (((x : SturmH lam), A x) : SturmH lam × SturmH lam)) =
        (A.graph : Set (SturmH lam × SturmH lam)) := by
    ext z
    change (∃ x : A.domain,
        (((x : SturmH lam), A x) : SturmH lam × SturmH lam) = z) ↔
      z ∈ A.graph
    exact (A.mem_graph_iff').symm
  have hEverySpectralGraphPoint :
      (S.graph : Set (SturmH lam × SturmH lam)) ⊆
        (A.graph.topologicalClosure :
          Set (SturmH lam × SturmH lam)) := by
    intro z hz
    obtain ⟨y, rfl⟩ := (S.mem_graph_iff').mp hz
    change (((y : SturmH lam), S y) : SturmH lam × SturmH lam) ∈
      closure (A.graph : Set (SturmH lam × SturmH lam))
    rw [← hGraphRange]
    apply (Metric.mem_closure_range_iff).2
    intro ε hε
    have hy : ((y : SturmH lam) - S y) ∈
        closure (Set.range (fun x : A.domain =>
          (x : SturmH lam) - A x)) := hDense _
    obtain ⟨x, hx⟩ :=
      (Metric.mem_closure_range_iff.mp hy)
        (ε / 3) (by positivity)
    obtain ⟨v, hv, hAv⟩ :=
      LinearPMap.exists_of_le hExt x
    have hpair :
        (((x : SturmH lam), A x) : SturmH lam × SturmH lam) =
          ((v : SturmH lam), S v) :=
      Prod.ext hv hAv
    have hshift :
        (x : SturmH lam) - A x =
          (v : SturmH lam) - S v := by
      rw [hv, hAv]
    have hcontrol :
        dist (((y : SturmH lam), S y) : SturmH lam × SturmH lam)
             (((x : SturmH lam), A x) : SturmH lam × SturmH lam) ≤
        3 * dist ((y : SturmH lam) - S y)
                 ((x : SturmH lam) - A x) := by
      calc
        _ = dist (((y : SturmH lam), S y) :
              SturmH lam × SturmH lam)
              (((v : SturmH lam), S v) :
              SturmH lam × SturmH lam) := by rw [hpair]
        _ ≤ 3 * dist ((y : SturmH lam) - S y)
                       ((v : SturmH lam) - S v) :=
          hGraphBound y v
        _ = _ := by rw [hshift]
    refine ⟨x, lt_of_le_of_lt hcontrol ?_⟩
    have hmul := mul_lt_mul_of_pos_left hx
      (by norm_num : (0 : ℝ) < 3)
    nlinarith
  have hForward : A.graph.topologicalClosure ≤ S.graph := by
    have hsub : (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        (S.graph : Set (SturmH lam × SturmH lam)) :=
      LinearPMap.le_graph_of_le hExt
    exact closure_minimal hsub hSclosed
  have hReverse : S.graph ≤ A.graph.topologicalClosure :=
    hEverySpectralGraphPoint
  apply LinearPMap.eq_of_eq_graph
  rw [← (sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph]
  exact le_antisymm hForward hReverse

/-- Equality of the complete (unbounded) operator domains, not just
an inclusion of graphs on polynomials. -/
theorem sturmRealPartialOperator_spectral_domain_eq_of_shift_graph_bound
    (lam : ℝ) (hlam : 0 < lam)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hSclosed : S.IsClosed)
    (hExt : sturmRealPartialOperator lam hlam ≤ S)
    (hGraphBound : ∀ x y : S.domain,
      dist (((x : SturmH lam), S x) : SturmH lam × SturmH lam)
           (((y : SturmH lam), S y) : SturmH lam × SturmH lam) ≤
        3 * dist ((x : SturmH lam) - S x)
                 ((y : SturmH lam) - S y)) :
    (sturmRealPartialOperator lam hlam).closure.domain = S.domain := by
  exact congrArg LinearPMap.domain
    (sturmRealPartialOperator_spectral_eq_closure_of_shift_graph_bound
      lam hlam S hSclosed hExt hGraphBound)

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_spectral_eq_closure_of_shift_graph_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_spectral_domain_eq_of_shift_graph_bound

end GegenbauerFock.Ultraspherical
