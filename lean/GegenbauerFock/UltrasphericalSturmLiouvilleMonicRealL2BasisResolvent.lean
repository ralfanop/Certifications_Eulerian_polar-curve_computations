import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes

/-!
# V007 — exact closed Sturm resolvent diagonal on normalized real L² Gegenbauer Hilbert basis

The explicitly constructed monic Gegenbauer eigenmodes already diagonalize
the true bounded positive resolvent of the closed real Sturm operator.
Their individually normalized HilbertBasis vectors have the same
eigenvalues by real linearity of the genuine resolvent. This statement
is therefore about an ACTUAL complete Hilbert basis, not just the dense
polynomial domain or an abstract putative eigenbasis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The full closed Sturm resolvent acts diagonally on each genuinely
normalized Gegenbauer L² eigenvector with its exact eigenvalue. -/
theorem sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  unfold sturmMonicEigenCandidate_realL2_normalized
  rw [map_smul, sturmMonicEigenCandidate_full_resolvent_diagonal
    lam t hlam ht n]
  exact smul_comm _ _ _

/-- The true complete real Gegenbauer HilbertBasis is a diagonal
eigenbasis for the actual all-L² closed Sturm positive resolvent. -/
theorem sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam n) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam n := by
  simpa only [sturmMonicEigenCandidate_realL2_hilbertBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot]
    using sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
      lam t hlam ht n

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal

end GegenbauerFock.Ultraspherical
