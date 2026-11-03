import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealSchattenBasis

/-!
# V007 — joint certified heat-generator, real S1 and S2 resolvent certificate

For the ACTUAL canonical Sturm closure on real weighted L², this single
theorem records five compatible kernel-checked operator statements:

1. Exact equality of the genuine heat semigroup generator graph with
   the canonical closure of the original polynomial differential operator.
2. Actual operator-norm summable real rank-one nuclear representation
   of the positive-shift resolvent.
3. Sharp projective real nuclear S1 cost: the infimum over ALL admissible
   real rank-one series equals the positive spectral trace.
4. Hilbert–Schmidt square-summability of actual resolvent images of the
   explicit COMPLETE normalized Gegenbauer Hilbert basis.
5. Exact squared HS mass on that basis (no scalar surrogate operators).

This is specifically a real-Hilbert nuclear and actual-basis S2
certificate. It does NOT silently assert equivalence with unrelated
complex Physlib / CFC ideals, or basis-independence of S2, which would
need an additional theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- One kernel-checkable statement for the complete generator and real
S1/S2 operator properties of the genuine Gegenbauer Sturm resolvent. -/
theorem sturmRealHeatGenerator_resolvent_realS1S2_joint_certificate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∀ f g : H lam,
      Tendsto
        (fun s : ℝ => s⁻¹ •
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
          (x : H lam) = f ∧
          (sturmRealPartialOperator lam hlam).closure x = g) ∧
    HasRealNuclearRankOneSeries
      (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    realNuclearInfimum
      (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      sturmResolventSpectralTrace lam t ∧
    IsRealHilbertSchmidtOnBasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht)
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) ∧
    (∑' n : ℕ,
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)‖ ^ 2) =
      sturmResolventSquaredSpectralTrace lam t := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g
    exact sturmRealHeatLimit_generator_exact_closedSturm_graph lam hlam f g
  · exact sturmRealClosedResolvent_has_real_nuclear_rank_one_series
      lam t hlam ht
  · exact sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace
      lam t hlam ht
  · exact sturmRealPositiveResolvent_isHS_on_actual_basis
      lam t hlam ht
  · unfold sturmResolventSquaredSpectralTrace
    apply tsum_congr
    intro n
    exact sturmRealPositiveResolvent_basis_norm_sq lam t hlam ht n

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatGenerator_resolvent_realS1S2_joint_certificate

end GegenbauerFock.Ultraspherical
