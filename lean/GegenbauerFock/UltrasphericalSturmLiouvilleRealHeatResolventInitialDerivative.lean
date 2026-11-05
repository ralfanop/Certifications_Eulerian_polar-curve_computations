import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — strong heat derivative for genuine resolvent-smoothed initial data

For every real weighted-L² input f and t>0, the actual closed Sturm
resolvent R_t f belongs to the domain of the canonical closed Sturm
operator. The fully kernel-certified heat generator identification
then gives its strong right derivative at zero:

  lim_{s↓0} (H_s R_t f - R_t f)/s = t R_t f - f.

This is a full-L² identity for arbitrary input data, not a statement
confined to polynomials or to a separately defined diagonal model.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The true full weighted-real-L² heat orbit starting from actual
positive Sturm resolvent data has an exact strong time-zero derivative. -/
theorem sturmRealHeat_resolvent_initial_right_derivative
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    Tendsto
      (fun s : ℝ => s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s
          (sturmRealPositiveResolventFullCLM lam t hlam ht f) -
          sturmRealPositiveResolventFullCLM lam t hlam ht f))
      (𝓝[>] (0 : ℝ))
      (𝓝 (t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f)) := by
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  let A := (sturmRealPartialOperator lam hlam).closure
  have hgraph :
      (R f, t • R f - f) ∈ (A.graph : Set (SturmH lam × SturmH lam)) :=
    sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f
  obtain ⟨x, hx⟩ := A.mem_graph_iff'.mp hgraph
  have hx1 : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have hx2 : A x = t • R f - f := congrArg Prod.snd hx
  exact (sturmRealHeatLimit_generator_exact_closedSturm_graph
    lam hlam (R f) (t • R f - f)).2 ⟨x, hx1, hx2⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_resolvent_initial_right_derivative

end GegenbauerFock.Ultraspherical
