import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventIntegratedCertificate

/-!
# V007 — single kernel-checkable closed Sturm generator and compact resolvent certificate

The C0 heat semigroup's full real-weighted-L2 right generator graph is
EXACTLY the canonical closure of the genuine polynomial Sturm operator.
Its positive-shift inverse is the compact spectral resolvent, with the
complete real spectrum and sharp finite-rank cutoff error.

Both component proofs are imported in ONE Lean module; this certifies
their joint compatibility rather than relying on independent CI runs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual full-L2 heat generator graph equals the canonical closed
polynomial Sturm graph; its genuine positive resolvent is compact with
exact spectral description and sharp finite-rank operator error. -/
theorem sturmRealHeatAndResolvent_joint_full_certificate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∀ f g : H lam,
      Tendsto
        (fun s : ℝ => s⁻¹ •
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
        ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
          (x : H lam) = f ∧
          (sturmRealPartialOperator lam hlam).closure x = g) ∧
    IsCompactOperator (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    (spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      ({0} : Set ℝ) ∪
        Set.range (fun n : ℕ =>
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹)) ∧
    (∀ N : ℕ,
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ =
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹) := by
  obtain ⟨hcompact, hspectrum, hcutoffs, _, _⟩ :=
    sturmRealClosedResolvent_compact_spectrum_and_exact_cutoffs
      lam t hlam ht
  exact ⟨
    (fun f g => sturmRealHeatLimit_generator_exact_closedSturm_graph
      lam hlam f g),
    hcompact, hspectrum, hcutoffs⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatAndResolvent_joint_full_certificate

end GegenbauerFock.Ultraspherical
