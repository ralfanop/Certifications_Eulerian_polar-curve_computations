import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventSelfAdjoint
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventPositive

/-!
# V007 — independent real positive spectral-S₁ criterion for the Sturm resolvent

This separates TWO descriptions of the ACTUAL real bounded operator:
(a) the real positive compact diagonal eigenvalue-summability criterion;
(b) the projective infimum over ALL real rank-one nuclear expansions.

The exact equality of these descriptions' trace values is now
kernel-certified via the general nuclear duality theorem. We make NO
claim of a general real CFC/Physlib absolute-value ideal equivalence:
the source-compatible Physlib API in this project is COMPLEX.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

/-- A real positive spectral S₁ presentation: the ACTUAL operator has a
complete orthonormal eigenbasis, nonnegative eigenvalues and a
summable eigenvalue sequence. Unlike a nuclear witness, this
definition involves an eigenbasis of the operator itself. -/
def HasRealPositiveS1Eigenbasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : Prop :=
  ∃ (b : HilbertBasis ℕ ℝ H) (σ : ℕ → ℝ),
    (∀ n, 0 ≤ σ n) ∧ Summable σ ∧
    (∀ n, T (b n) = σ n • b n)

/-- Abstract real positive spectral S₁ membership implies the
positive trace summability condition in its OWN complete eigenbasis. -/
theorem HasRealPositiveS1Eigenbasis.exists_trace_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : H →L[ℝ] H}
    (hT : HasRealPositiveS1Eigenbasis T) :
    ∃ b : HilbertBasis ℕ ℝ H,
      IsRealPositiveTraceSummableOnBasis T b := by
  obtain ⟨b, σ, hnonneg, hs, heig⟩ := hT
  refine ⟨b, ?_⟩
  unfold IsRealPositiveTraceSummableOnBasis
  have hdiag (n : ℕ) :
      inner ℝ (b n) (T (b n)) = σ n := by
    rw [heig n, real_inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
    ring
  exact hs.congr (fun n => (hdiag n).symm)

/-- The ACTUAL complete real Gegenbauer Hilbert basis supplies a
positive summable eigenvalue sequence for the closed Sturm resolvent. -/
theorem sturmRealClosedResolvent_has_positive_real_spectralS1
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    HasRealPositiveS1Eigenbasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  refine ⟨sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam,
    (fun n : ℕ =>
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹), ?_, ?_, ?_⟩
  · intro n
    exact le_of_lt (sturmResolventMultiplier_pos lam t hlam ht n)
  · exact sturmResolventMultiplier_summable lam t hlam ht
  · intro n
    exact sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal
      lam t hlam ht n

/-- The spectral positive S₁ criterion and the general nuclear
projective S₁ norm coincide ON THE ACTUAL CLOSED STURM RESOLVENT.
The right side is the diagonal trace in an independently constructed
complete real Hilbert eigenbasis. -/
theorem sturmRealClosedResolvent_realS1_spectral_nuclear_bridge
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    HasRealPositiveS1Eigenbasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      ∑' n : ℕ,
        inner ℝ
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
          (sturmRealPositiveResolventFullCLM lam t hlam ht
            ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)) := by
  constructor
  · exact sturmRealClosedResolvent_has_positive_real_spectralS1
      lam t hlam ht
  · exact
      (sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace
        lam t hlam ht).trans
      (sturmRealPositiveResolvent_actual_basis_trace_eq
        lam t hlam ht).symm

/-- Positive, selfadjoint, positive-spectral-S₁, and exact projective
nuclear norm: the four properties concern the SAME genuine real
closed Sturm resolvent, not an auxiliary model. -/
theorem sturmRealClosedResolvent_realS1_integrated_certificate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsSelfAdjoint (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    (∀ f : Lp ℝ 2 (measure lam),
      0 ≤ inner ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht f) f) ∧
    HasRealPositiveS1Eigenbasis
      (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      sturmResolventSpectralTrace lam t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sturmRealPositiveResolventFullCLM_isSelfAdjoint lam t hlam ht
  · intro f
    exact sturmRealPositiveResolventFullCLM_inner_nonneg lam t hlam ht f
  · exact sturmRealClosedResolvent_has_positive_real_spectralS1
      lam t hlam ht
  · exact sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace
      lam t hlam ht

#print axioms GegenbauerFock.Ultraspherical.HasRealPositiveS1Eigenbasis.exists_trace_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_has_positive_real_spectralS1
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_realS1_spectral_nuclear_bridge
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_realS1_integrated_certificate

end GegenbauerFock.Ultraspherical
