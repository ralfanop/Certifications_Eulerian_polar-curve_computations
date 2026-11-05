import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorClosedDomainForward
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorReverseDomain

/-!
# V007 — the genuine heat infinitesimal generator IS the canonical closed Sturm operator

This theorem combines two independently proved graph inclusions into
equality of the complete unbounded graphs, INCLUDING THEIR DOMAINS.

For lambda>0, the right norm-L2 derivative of the actual C0 contraction
semigroup H_s exists for f with value g if and only if f belongs to the
domain of the genuine canonical graph closure of the polynomial
Sturm differential operator and g equals that closure applied to f.

No spectral extension, formal coefficient model or unsupported axiom
is substituted for the actual closed differential operator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Equality of the full right-infinitesimal-generator graph with the
actual canonical closed Gegenbauer Sturm operator graph. -/
theorem sturmRealHeatLimit_generator_exact_closedSturm_graph
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam) :
    Tendsto
      (fun s : ℝ => s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
      ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
        (x : SturmH lam) = f ∧
        (sturmRealPartialOperator lam hlam).closure x = g := by
  constructor
  · intro hd
    exact sturmRealHeatLimit_generator_graph_subset_closedSturm
      lam hlam f g hd
  · rintro ⟨x, rfl, rfl⟩
    exact sturmRealHeatLimit_closed_sturm_right_derivative lam hlam x

/-- The graph is equal as a set of pairs in the genuine weighted real L2. -/
theorem sturmRealHeatLimit_generator_graph_set_eq_closedSturm
    (lam : ℝ) (hlam : 0 < lam) :
    { p : SturmH lam × SturmH lam |
      Tendsto
        (fun s : ℝ => s⁻¹ •
          (sturmRealHeatLimitNonnegativeExtended lam hlam s p.1 - p.1))
        (𝓝[>] (0 : ℝ)) (𝓝 p.2) } =
    { p : SturmH lam × SturmH lam |
      ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
        (x : SturmH lam) = p.1 ∧
        (sturmRealPartialOperator lam hlam).closure x = p.2 } := by
  ext p
  exact sturmRealHeatLimit_generator_exact_closedSturm_graph
    lam hlam p.1 p.2

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_exact_closedSturm_graph
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_graph_set_eq_closedSturm

end GegenbauerFock.Ultraspherical
