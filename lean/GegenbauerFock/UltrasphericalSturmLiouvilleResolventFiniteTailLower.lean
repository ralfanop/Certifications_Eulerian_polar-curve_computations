import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTruncationApply
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2BasisResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — sharp spectral-tail lower bound on the actual closed Sturm resolvent

The first omitted normalized Gegenbauer mode is annihilated by the
finite-rank spectral truncation and is an exact eigenvector of the
genuine closed Sturm resolvent. It attains the expected tail error,
establishing the *lower* operator-norm estimate. An independent
Parseval upper bound is required for equality and compactness.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The first omitted normalized eigenmode is killed by truncation. -/
theorem sturmRealResolventFiniteRankTruncation_omitted
    (lam t : ℝ) (hlam : 0 < lam) (N : ℕ) :
    sturmRealResolventFiniteRankTruncation lam t hlam N
      (sturmMonicEigenCandidate_realL2_normalized lam hlam N) = 0 := by
  rw [sturmRealResolventFiniteRankTruncation_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hnlt : n < N := Finset.mem_range.mp hn
  have hne : n ≠ N := ne_of_lt hnlt
  have horth :=
    (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam).inner_eq_zero hne
  rw [horth, zero_smul, smul_zero]

/-- Lower bound for the exact full-operator truncation error,
achieved on the first omitted normalized eigenfunction. -/
theorem sturmRealClosedResolvent_finite_tail_norm_ge
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ ≤
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ := by
  let e : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam N
  let B : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht -
      sturmRealResolventFiniteRankTruncation lam t hlam N
  have he : ‖e‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam N
  have hR := sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal
    lam t hlam ht N
  have hT := sturmRealResolventFiniteRankTruncation_omitted lam t hlam N
  have hBe :
      B e = (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ • e := by
    change (sturmRealPositiveResolventFullCLM lam t hlam ht -
      sturmRealResolventFiniteRankTruncation lam t hlam N) e = _
    rw [ContinuousLinearMap.sub_apply, hR, hT, sub_zero]
  have hbeta : 0 < (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ :=
    sturmResolventMultiplier_pos lam t hlam ht N
  have hnorm :
      ‖B e‖ = (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ := by
    rw [hBe, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hbeta]
  have hle := B.le_opNorm e
  rw [hnorm, he, mul_one] at hle
  exact hle

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_omitted
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_finite_tail_norm_ge

end GegenbauerFock.Ultraspherical
