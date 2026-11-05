import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTruncationApply
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates

/-!
# V007 — finite Gegenbauer resolvent coordinates on actual weighted L²

Each finite-rank truncation has the exact truncated multiplier on
the true normalized Gegenbauer Hilbert coordinates. This isolates
the coefficient identity needed for the sharp operator-norm tail.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- All Fourier coordinates of the true finite rank resolvent
truncation, with the exact cutoff at N. -/
theorem sturmRealResolventFiniteRankTruncation_repr_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (N : ℕ)
    (f : SturmH lam) (k : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealResolventFiniteRankTruncation lam t hlam N f) k =
    if k < N then
      (t + (k : ℝ) * ((k : ℝ) + 2 * lam))⁻¹ *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f k
    else 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hb (n : ℕ) :
      b n = sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hfinite :
      sturmRealResolventFiniteRankTruncation lam t hlam N f =
        ∑ n ∈ Finset.range N,
          ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
            b.repr f n) • b n := by
    rw [sturmRealResolventFiniteRankTruncation_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← hb n]
    rw [← b.repr_apply_apply]
    exact smul_smul _ _ _
  rw [HilbertBasis.repr_apply_apply, hfinite]
  by_cases hk : k < N
  · simp only [if_pos hk]
    exact b.orthonormal.inner_right_sum
      (fun n => ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
        b.repr f n)) (Finset.mem_range.mpr hk)
  · simp only [if_neg hk]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro n hn
    rw [inner_smul_right]
    have hne : k ≠ n := by
      have hlt : n < N := Finset.mem_range.mp hn
      omega
    rw [b.orthonormal.inner_eq_zero hne]
    simp

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_repr_diagonal

end GegenbauerFock.Ultraspherical
