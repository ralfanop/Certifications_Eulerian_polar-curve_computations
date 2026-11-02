import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTruncationApply
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates

/-!
# V007 — exact Fourier-coordinate formula for finite spectral Sturm truncations

On every input of the genuine weighted real L², the rank-N truncation has
the exact first N diagonal resolvent coefficients, with all subsequent
coordinates zero. This supplies the missing coordinate comparison for
the operator-norm tail estimate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

/-- Fourier coordinates of the genuine rank-N resolvent truncation are
the first N exact resolvent multipliers times the input coordinates. -/
theorem sturmRealResolventFiniteRankTruncation_repr_coordinate
    (lam t : ℝ) (hlam : 0 < lam) (N k : ℕ)
    (f : Lp ℝ 2 (measure lam)) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealResolventFiniteRankTruncation lam t hlam N f) k =
      if k < N then
        (t + (k : ℝ) * ((k : ℝ) + 2 * lam))⁻¹ *
          (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f k
      else 0 := by
  classical
  let e := sturmMonicEigenCandidate_realL2_normalized lam hlam
  have hv : Orthonormal ℝ e :=
    sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam
  simp only [HilbertBasis.repr_apply_apply,
    sturmMonicEigenCandidate_realL2_hilbertBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [sturmRealResolventFiniteRankTruncation_apply]
  change inner ℝ (e k)
    (∑ n ∈ Finset.range N,
       (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
         (inner ℝ (e n) f • e n)) =
    if k < N then
      (t + (k : ℝ) * ((k : ℝ) + 2 * lam))⁻¹ *
        inner ℝ (e k) f
    else 0
  by_cases hk : k < N
  · rw [if_pos hk]
    have h :=
      hv.inner_right_sum
        (fun n : ℕ =>
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ * inner ℝ (e n) f)
        (Finset.mem_range.mpr hk)
    simpa only [smul_smul] using h
  · rw [if_neg hk, inner_sum]
    apply Finset.sum_eq_zero
    intro n hn
    have hneq : k ≠ n := by
      intro hkn
      subst n
      exact hk (Finset.mem_range.mp hn)
    have hz : inner ℝ (e k) (e n) = 0 := hv.inner_eq_zero hneq
    simp only [inner_smul_right, hz, mul_zero]

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_repr_coordinate

end GegenbauerFock.Ultraspherical
