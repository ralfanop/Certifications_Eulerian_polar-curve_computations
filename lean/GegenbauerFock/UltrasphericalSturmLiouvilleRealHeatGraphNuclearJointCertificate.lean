import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatClosedGraphStrongContinuity
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatNuclearClass

/-!
# V007 — joint canonical Sturm graph and genuine heat nuclear certificate

This theorem assembles, for the ACTUAL weighted-real-L² Gegenbauer
semigroup, the following independently kernel-proved statements:

* strong right continuity at zero in the canonical closed Sturm
  graph norm (not just the Hilbert-space L² norm);
* compactness at every strictly positive time;
* membership in the general real-Hilbert nuclear rank-one series class;
* equality of the positive spectral rank-one nuclear mass with the
  actual Gegenbauer Hilbert-basis diagonal trace.

The canonical closed differential Sturm operator, not an abstract
stand-in, occurs in the first conjunct. The remaining conjuncts
concern the genuine bounded heat operator constructed by strong
Yosida limits on ALL of weighted real L².

The universal projective infimum among ALL nuclear representations
is a separate stronger statement, not silently inferred here.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace Filter
open scoped Topology

private abbrev JointHeatH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Integrated full-space heat certificate: canonical closed Sturm graph
continuity, positive-time compactness, real nuclear class, and exact
positive nuclear witness mass versus actual basis trace. -/
theorem sturmRealHeat_closed_graph_compact_nuclear_joint_certificate
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    (∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
      Tendsto
        (fun u : ℝ =>
          ‖sturmRealHeatLimitNonnegativeExtended lam hlam u
              (x : JointHeatH lam) - (x : JointHeatH lam)‖ +
          ‖sturmRealHeatLimitNonnegativeExtended lam hlam u
              ((sturmRealPartialOperator lam hlam).closure x) -
            (sturmRealPartialOperator lam hlam).closure x‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ))) ∧
    IsCompactOperator
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) ∧
    HasRealNuclearRankOneSeries
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) ∧
    (∑' n : ℕ,
      ‖Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
    (∑' n : ℕ,
      inner ℝ
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
        (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) := by
  exact ⟨
    sturmRealHeatLimit_closed_graph_norm_tendsto_zero lam hlam,
    sturmRealHeat_positive_time_isCompactOperator lam s hlam hs,
    sturmRealHeat_has_real_nuclear_rank_one_series lam s hlam hs,
    sturmRealHeat_positive_nuclear_mass_eq_actual_basis_trace
      lam s hlam hs⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_closed_graph_compact_nuclear_joint_certificate

end GegenbauerFock.Ultraspherical
