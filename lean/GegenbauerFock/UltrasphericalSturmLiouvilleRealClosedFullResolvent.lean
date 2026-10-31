import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveResolventFullCLM
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedPositiveShiftBounds

/-!
# V007 — full-real-Hilbert resolvent solves the ACTUAL closed Sturm equation

The exact finite-polynomial inverse of (tI-A₀), t>0, is bounded
on the dense polynomial image in L²(νλ;ℝ). Its certified continuous
extension to all of L² is R_t.

For each polynomial f, (R_t f, tR_t f-f) is in the graph of A₀
and hence in the graph of its canonical closure. Since both the
extended inverse and f ↦ tR_t f-f are continuous, and the graph
of the canonical closure is closed, this identity extends to ALL
f in the actual complete weighted real Hilbert space.

Thus the positive shift of the genuine closed Sturm operator is
surjective and has the already certified trivial kernel.
The bounded full-Hilbert operator R_t is its actual inverse.
This proof does not assume existence of a spectral eigenbasis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev D (lam : ℝ) (hlam : 0 < lam) :=
  sturmRealPolynomialDomain lam hlam

/-- Graph relation for every polynomial datum, using the exact
finite polynomial positive shifted inverse and the actual closed
Sturm graph inclusion. -/
theorem sturmRealPositiveResolventFullCLM_core_graph
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : D lam hlam) :
    (((sturmRealPositiveResolventFullCLM lam t hlam ht
          (f : SturmH lam)),
       t • sturmRealPositiveResolventFullCLM lam t hlam ht
          (f : SturmH lam) - (f : SturmH lam)) :
          SturmH lam × SturmH lam) ∈
      (sturmRealPartialOperator lam hlam).closure.graph := by
  let A := sturmRealPartialOperator lam hlam
  let u : D lam hlam :=
    sturmRealDomainPositiveResolvent lam t hlam ht f
  have hcore :
      sturmRealPositiveResolventFullCLM lam t hlam ht
          (f : SturmH lam) = (u : SturmH lam) :=
    sturmRealPositiveResolventFullCLM_onCore lam t hlam ht f
  have hpoly : t • (u : SturmH lam) - A u = (f : SturmH lam) := by
    have hv := congrArg Subtype.val
      (sturmRealDomainPositiveShift_resolvent lam t hlam ht f)
    simpa [sturmRealDomainPositiveShift, sturmRealPartialOperator_apply, u]
      using hv
  have himage : t • (u : SturmH lam) - (f : SturmH lam) = A u := by
    calc
      t • (u : SturmH lam) - (f : SturmH lam) =
        t • (u : SturmH lam) -
          (t • (u : SturmH lam) - A u) := by rw [hpoly]
      _ = A u := by abel
  change ((sturmRealPositiveResolventFullCLM lam t hlam ht
      (f : SturmH lam),
    t • sturmRealPositiveResolventFullCLM lam t hlam ht
      (f : SturmH lam) - (f : SturmH lam)) :
      SturmH lam × SturmH lam) ∈ A.closure.graph
  rw [hcore, himage]
  exact (LinearPMap.le_graph_of_le
    (sturmRealPartialOperator_le_closed_extension lam hlam))
      (A.mem_graph u)

/-- The actual positive full-Hilbert resolvent yields a point in
the graph of the canonical closed Sturm operator for EVERY L² datum. -/
theorem sturmRealPositiveResolventFullCLM_closed_graph
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    ((sturmRealPositiveResolventFullCLM lam t hlam ht f,
      t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f) :
        SturmH lam × SturmH lam) ∈
      (sturmRealPartialOperator lam hlam).closure.graph := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hcont : Continuous
      (fun g : SturmH lam => ((R g, t • R g - g) :
        SturmH lam × SturmH lam)) := by
    fun_prop
  have hclosed : IsClosed
      (A.closure.graph : Set (SturmH lam × SturmH lam)) :=
    sturmRealPartialOperator_closure_isClosed lam hlam
  have hpreimage : IsClosed
      ((fun g : SturmH lam => ((R g, t • R g - g) :
        SturmH lam × SturmH lam)) ⁻¹
          (A.closure.graph : Set (SturmH lam × SturmH lam))) :=
    hclosed.preimage hcont
  have hsub :
      (D lam hlam : Set (SturmH lam)) ⊆
        (fun g : SturmH lam => ((R g, t • R g - g) :
          SturmH lam × SturmH lam)) ⁻¹
            (A.closure.graph : Set (SturmH lam × SturmH lam)) := by
    intro g hg
    let x : D lam hlam := ⟨g, hg⟩
    change ((R g, t • R g - g) :
      SturmH lam × SturmH lam) ∈ A.closure.graph
    simpa only [show (x : SturmH lam) = g from rfl] using
      sturmRealPositiveResolventFullCLM_core_graph lam t hlam ht x
  have hdense :
      Dense (D lam hlam : Set (SturmH lam)) :=
    sturmRealPolynomialDomain_dense_set lam hlam
  exact (closure_minimal hsub hpreimage) (hdense f)

/-- Every real weighted L² datum is attained by the positive shift
tI - closure(A₀) of the genuine canonical closed Sturm operator. -/
theorem sturmRealClosedPositiveShift_surjective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Surjective
      (fun x : (sturmRealPartialOperator lam hlam).closure.domain =>
        t • (x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x) := by
  intro f
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hgraph := sturmRealPositiveResolventFullCLM_closed_graph
    lam t hlam ht f
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp hgraph
  have hfirst : (x : SturmH lam) = R f :=
    congrArg Prod.fst hx
  have hsecond : A.closure x = t • R f - f :=
    congrArg Prod.snd hx
  refine ⟨x, ?_⟩
  change t • (x : SturmH lam) - A.closure x = f
  rw [hfirst, hsecond]
  abel

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_core_graph
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_closed_graph
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPositiveShift_surjective

end GegenbauerFock.Ultraspherical
