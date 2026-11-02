import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventQuadraticDecay

/-!
# V007 — quadratic operator-norm spectral cutoff accuracy

The genuine real weighted-L² closed Gegenbauer Sturm resolvent has
exact spectral cutoff error 1/(t+N(N+2λ)). For N ≥ 1 this is at most
1/N² uniformly in both positive parameters. This produces an explicit,
non-asymptotic error estimate for every source in the full Hilbert space.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Operator-norm O(N⁻²) approximation of the genuine compact
Sturm resolvent by its finite-rank spectral truncation. -/
theorem sturmRealClosedResolvent_quadratic_operator_cutoff_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ ≤
      ((N : ℝ) ^ 2)⁻¹ := by
  rw [sturmRealClosedResolvent_finite_tail_norm_eq]
  exact sturmResolventMultiplier_le_inv_degree_sq lam t hlam ht N hN

/-- Full weighted-real-L² sourcewise O(N⁻²) estimate, without an
assumption of additional regularity of the input source. -/
theorem sturmRealClosedResolvent_quadratic_vector_cutoff_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N : ℕ) (hN : 1 ≤ N) (f : SturmH lam) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
        sturmRealResolventFiniteRankTruncation lam t hlam N f‖ ≤
      ((N : ℝ) ^ 2)⁻¹ * ‖f‖ := by
  let B : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht -
      sturmRealResolventFiniteRankTruncation lam t hlam N
  have hB :
      ‖B‖ ≤ ((N : ℝ) ^ 2)⁻¹ :=
    sturmRealClosedResolvent_quadratic_operator_cutoff_bound
      lam t hlam ht N hN
  have happly : ‖B f‖ ≤ ‖B‖ * ‖f‖ := B.le_opNorm f
  calc
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
        sturmRealResolventFiniteRankTruncation lam t hlam N f‖ =
      ‖B f‖ := by
        simp only [B, ContinuousLinearMap.sub_apply]
    _ ≤ ‖B‖ * ‖f‖ := happly
    _ ≤ ((N : ℝ) ^ 2)⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_right hB (norm_nonneg _)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_quadratic_operator_cutoff_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_quadratic_vector_cutoff_bound

end GegenbauerFock.Ultraspherical
