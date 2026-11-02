import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorReverseCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorGraphBridge

/-!
# V007 — strong heat generator domain is contained in canonical Sturm closure domain

The canonical weighted-real-L² Sturm graph has already been proved
to equal the exact Gegenbauer diagonal spectral realization, INCLUDING
the whole weighted-ℓ² domain. If a heat orbit has an L² right derivative
g, the previously formalized coordinate limit says
  (b.repr g)_n = -n(n+2λ) (b.repr f)_n.
The ℓ² vector -(b.repr g) witnesses spectral-domain membership of f.

Thus the right-generator graph is contained in the canonical closed
polynomial Sturm graph, with equality of both the point and its action.
The opposite graph inclusion remains a separate theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A genuine L² right derivative of the full heat orbit forces
membership in the *canonical closed differential Sturm domain* and
identifies the derivative with the closed Sturm action. -/
theorem sturmRealHeatLimit_generator_graph_subset_closedSturm
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam)
    (hderiv : Tendsto
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g)) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) = f ∧
        (sturmRealPartialOperator lam hlam).closure x = g := by
  apply sturmRealClosed_graph_of_diagonal_coefficients lam hlam f g
  intro n
  calc
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g n =
        (-((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n :=
      sturmRealHeatLimit_right_derivative_repr lam hlam f g hderiv n
    _ = (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
      ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_graph_subset_closedSturm

end GegenbauerFock.Ultraspherical
