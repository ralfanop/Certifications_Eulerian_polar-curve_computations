import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGraphNuclearJointCertificate
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatNuclearProjectiveTrace

/-!
# V007 — final real heat certificate: closed graph, compactness, nuclearity, sharp S1

This composes five independently kernel-checked results for the GENUINE
Gegenbauer heat semigroup on the ACTUAL real weighted L²:

* strong right continuity at zero in the canonical closed Sturm graph norm;
* compactness of H_s for every strictly positive time;
* a general absolutely summable real-Hilbert nuclear rank-one series;
* equality of the mass of its explicit positive orthogonal series and
  the actual Gegenbauer Hilbert-basis diagonal trace;
* EXACT projective real S1 nuclear infimum, minimized over ALL admissible
  real rank-one representations, equal to the heat spectral trace.

The last equality is the universal S1 result, and is NOT inferred merely
from the exhibited positive nuclear expansion. Its lower bound uses a
separate full finite-trace duality argument. No complex CFC/Physlib
trace-class equivalence is assumed in this theorem.

The canonical differential operator is the closure of the actual
polynomial Gegenbauer Sturm operator, not an auxiliary diagonal stand-in.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace Filter
open scoped Topology

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- All five full-space real Gegenbauer heat conclusions in a single
kernel-checkable theorem, including the universal sharp real S1 norm. -/
theorem sturmRealHeat_closed_graph_compact_nuclear_exactS1_joint_certificate
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    (∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
      Tendsto
        (fun u : ℝ =>
          ‖sturmRealHeatLimitNonnegativeExtended lam hlam u
              (x : H lam) - (x : H lam)‖ +
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
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) ∧
    realNuclearInfimum
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
      ∑' n : ℕ,
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  obtain ⟨hgraph, hcompact, hnuclear, hmass⟩ :=
    sturmRealHeat_closed_graph_compact_nuclear_joint_certificate
      lam s hlam hs
  exact ⟨hgraph, hcompact, hnuclear, hmass,
    sturmRealHeat_realNuclearInfimum_eq_spectralTrace_directDuality
      lam s hlam hs⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_closed_graph_compact_nuclear_exactS1_joint_certificate

end GegenbauerFock.Ultraspherical
