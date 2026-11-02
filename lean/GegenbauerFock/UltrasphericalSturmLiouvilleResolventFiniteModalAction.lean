import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTruncationApply
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis

/-!
# V007 — exact finite-rank Sturm resolvent action on every Gegenbauer mode

The actual finite rank spectral truncation agrees with the full resolvent
on basis modes below the cutoff and annihilates every basis mode from
the cutoff onward. This is proved without assuming compactness of
the full resolvent and supplies the algebraic input for the operator
norm approximation theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The finite rank genuine weighted-L² Sturm resolvent has the
exact spectral cutoff action on each normalized basis eigenvector. -/
theorem sturmRealResolventFiniteRankTruncation_mode_eq_ite
    (lam t : ℝ) (hlam : 0 < lam) (N k : ℕ) :
    sturmRealResolventFiniteRankTruncation lam t hlam N
      (sturmMonicEigenCandidate_realL2_normalized lam hlam k) =
        if k < N then
          (t + (k : ℝ) * ((k : ℝ) + 2 * lam))⁻¹ •
            sturmMonicEigenCandidate_realL2_normalized lam hlam k
        else 0 := by
  classical
  rw [sturmRealResolventFiniteRankTruncation_apply]
  by_cases hk : k < N
  · rw [if_pos hk]
    have hmem : k ∈ Finset.range N := Finset.mem_range.mpr hk
    rw [Finset.sum_eq_single k]
    · have heq :
          inner ℝ
            (sturmMonicEigenCandidate_realL2_normalized lam hlam k)
            (sturmMonicEigenCandidate_realL2_normalized lam hlam k) = 1 := by
        rw [real_inner_self_eq_norm_sq,
          sturmMonicEigenCandidate_realL2_normalized_norm]
        norm_num
      simp only [heq, one_smul]
    · intro n hn hne
      have hz :=
        (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam).inner_eq_zero hne
      rw [hz, zero_smul, smul_zero]
    · intro hnot
      exact (hnot hmem).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro n hn
    have hne : n ≠ k := by
      intro heq
      subst k
      exact hk (Finset.mem_range.mp hn)
    have hz :=
      (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam).inner_eq_zero hne
    rw [hz, zero_smul, smul_zero]

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_mode_eq_ite

end GegenbauerFock.Ultraspherical
