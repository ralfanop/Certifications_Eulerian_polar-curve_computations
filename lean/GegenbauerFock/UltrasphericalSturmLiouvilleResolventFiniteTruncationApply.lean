import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteRankTruncations
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis

/-!
# V007 — explicit action of finite Gegenbauer resolvent truncations

The finite operator constructed from normalized rank-one Gegenbauer
projectors acts as the expected finite spectral sum on every vector of
the *actual* real ultraspherical L². This is the algebraic bridge
between finite-rank operator sums and the certified infinite spectral
HasSum formula, without assuming any compactness result.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Explicit pointwise finite spectral synthesis of the genuine
bounded truncation operator. -/
theorem sturmRealResolventFiniteRankTruncation_apply
    (lam t : ℝ) (hlam : 0 < lam) (N : ℕ) (f : SturmH lam) :
    sturmRealResolventFiniteRankTruncation lam t hlam N f =
      ∑ n ∈ Finset.range N,
        (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
          (inner ℝ
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n) f •
              sturmMonicEigenCandidate_realL2_normalized lam hlam n) := by
  simp only [sturmRealResolventFiniteRankTruncation,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply]

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_apply

end GegenbauerFock.Ultraspherical
