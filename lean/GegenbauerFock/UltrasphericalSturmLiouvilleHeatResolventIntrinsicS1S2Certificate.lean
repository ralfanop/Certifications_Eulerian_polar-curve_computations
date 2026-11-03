import GegenbauerFock.UltrasphericalSturmLiouvilleHeatResolventS1S2JointCertificate
import GegenbauerFock.UltrasphericalSturmLiouvilleRealS2BasisGeneral

/-!
# V007 — intrinsic real S1/S2 canonical Sturm resolvent certificate

This theorem combines already independently kernel-certified full-space
operator theorems with the new arbitrary-real-Hilbert-basis HS invariant.
It treats the actual positive-shift resolvent of the canonical closure
of the polynomial Gegenbauer Sturm differential operator.

The projective REAL nuclear S1 norm is exactly the spectral trace; the
S2 squared image energy is exactly the squared spectral trace on EVERY
complete real Hilbert basis, regardless of its index type. The genuine
heat-semigroup generator graph is exactly the original Sturm closure.

There is no hidden identification with a COMPLEX trace-class predicate
or use of an auxiliary abstract spectral extension.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The joint complete weighted-real-L2 Sturm generator and intrinsic
S1/S2 certificate, for any chosen complete real Hilbert basis. -/
theorem sturmRealHeatGenerator_resolvent_intrinsicS1S2_joint_certificate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {ι : Type*} (c : HilbertBasis ι ℝ (H lam)) :
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
    HasSum
      (fun i : ι =>
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht (c i)‖ ^ 2)
      (sturmResolventSquaredSpectralTrace lam t) := by
  obtain ⟨hgen, hnuc, hS1, _, _⟩ :=
    sturmRealHeatGenerator_resolvent_realS1S2_joint_certificate
      lam t hlam ht
  exact ⟨hgen, hnuc, hS1,
    sturmRealClosedResolvent_hsMass_general_basis lam t hlam ht c⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatGenerator_resolvent_intrinsicS1S2_joint_certificate

end GegenbauerFock.Ultraspherical
