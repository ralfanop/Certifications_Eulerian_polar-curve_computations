import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis

/-!
# V007 — the genuine Gegenbauer unitary Fourier transform on real weighted L²

The preceding certified orthogonal modes have been normalized to a Hilbert
basis. Its built-in representation is now the *surjective* linear isometry
from genuine weighted real L² to all of ℓ²(ℕ, ℝ).

Unlike the unnormalized injective coefficient map, this transform includes
the precise norm scaling and is onto arbitrary square-summable sequences.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The all-degree normalized real Gegenbauer Fourier transform is a
surjective linear isometry onto the genuine real square-summable sequences. -/
noncomputable def sturmMonicEigenCandidate_realL2_unitary
    (lam : ℝ) (hlam : 0 < lam) :
    SturmH lam ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr

/-- Its nth coordinate is the genuine weighted-L² Fourier coefficient
against the explicitly normalized degree-n Gegenbauer eigenvector. -/
theorem sturmMonicEigenCandidate_realL2_unitary_apply
    (lam : ℝ) (hlam : 0 < lam)
    (f : SturmH lam) (n : ℕ) :
    sturmMonicEigenCandidate_realL2_unitary lam hlam f n =
      inner ℝ (sturmMonicEigenCandidate_realL2_normalized lam hlam n) f := by
  have hb :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n =
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
    unfold sturmMonicEigenCandidate_realL2_hilbertBasis
    exact congrFun
      (HilbertBasis.coe_mkOfOrthogonalEqBot
        (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam)
        (sturmMonicEigenCandidate_realL2_normalized_orthogonal_eq_bot lam hlam)) n
  change (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n = _
  simpa only [hb] using
    (HilbertBasis.repr_apply_apply
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) f n)

/-- Exact Parseval norm equality for every genuine real weighted-L² vector. -/
theorem sturmMonicEigenCandidate_realL2_unitary_norm
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    ‖sturmMonicEigenCandidate_realL2_unitary lam hlam f‖ = ‖f‖ :=
  (sturmMonicEigenCandidate_realL2_unitary lam hlam).norm_map f

/-- Every real ℓ² sequence is the Fourier image of its inverse synthesis. -/
theorem sturmMonicEigenCandidate_realL2_unitary_surjective
    (lam : ℝ) (hlam : 0 < lam)
    (a : lp (fun _ : ℕ => ℝ) 2) :
    sturmMonicEigenCandidate_realL2_unitary lam hlam
      ((sturmMonicEigenCandidate_realL2_unitary lam hlam).symm a) = a := by
  exact (sturmMonicEigenCandidate_realL2_unitary lam hlam).apply_symm_apply a

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_unitary
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_unitary_apply
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_unitary_norm
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_unitary_surjective

end GegenbauerFock.Ultraspherical
