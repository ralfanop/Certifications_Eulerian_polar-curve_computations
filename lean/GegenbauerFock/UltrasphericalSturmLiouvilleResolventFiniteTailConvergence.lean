import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — operator-norm convergence of genuine Gegenbauer resolvent truncations

The exact operator-norm truncation error, proved for the *actual closed*
weighted-real-L² Sturm resolvent, implies that its finite-rank Gegenbauer
spectral cutoffs converge in the continuous-linear-map operator norm.

This is strictly stronger than pointwise convergence on every fixed input;
the convergence is uniform on the unit ball and makes the compactness
argument quantitative without a separate unproved tail hypothesis.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter

/-- The genuine finite-rank Gegenbauer spectral resolvents converge in
operator norm to the positive resolvent of the canonical *closed*
Sturm differential operator, on actual weighted real L². -/
theorem sturmRealClosedResolvent_finite_truncation_tendsto_opNorm
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto
      (fun N : ℕ => sturmRealResolventFiniteRankTruncation lam t hlam N)
      atTop
      (𝓝 (sturmRealPositiveResolventFullCLM lam t hlam ht)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbeta :=
    sturmResolventMultiplier_tendsto_zero lam t hlam ht
  have heq (N : ℕ) :
      ‖sturmRealResolventFiniteRankTruncation lam t hlam N -
          sturmRealPositiveResolventFullCLM lam t hlam ht‖ =
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ := by
    rw [norm_sub_rev]
    exact sturmRealClosedResolvent_finite_tail_norm_eq lam t hlam ht N
  simpa only [heq] using hbeta

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_finite_truncation_tendsto_opNorm

end GegenbauerFock.Ultraspherical
