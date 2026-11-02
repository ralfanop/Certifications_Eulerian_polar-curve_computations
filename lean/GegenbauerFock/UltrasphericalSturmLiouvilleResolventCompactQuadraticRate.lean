import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventQuadraticDecay

/-!
# V007 — quantitative compact canonical Sturm resolvent

The previously certified exact norm of the spectral truncation error,
together with the verified quadratic scalar decay, gives an explicit
operator-norm O(N^-2) approximation rate. We also record the
unconditional convergence in operator norm of the actual finite rank
truncations to the canonical closed Sturm resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Quantitative rank-N approximation of the genuine closed real
Sturm resolvent, uniformly in the positive parameters lambda and t. -/
theorem sturmRealClosedResolvent_finite_tail_quadratic_rate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
      sturmRealResolventFiniteRankTruncation lam t hlam N‖ ≤
        ((N : ℝ) ^ 2)⁻¹ := by
  rw [sturmRealClosedResolvent_finite_tail_norm_eq lam t hlam ht N]
  exact sturmResolventMultiplier_le_inv_degree_sq lam t hlam ht N hN

/-- Explicit finite rank spectral truncations converge in
operator norm to the genuine canonical closed Sturm resolvent. -/
theorem sturmRealClosedResolvent_truncations_tendsto_opNorm
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto
      (fun N : ℕ => sturmRealResolventFiniteRankTruncation lam t hlam N)
      atTop
      (nhds (sturmRealPositiveResolventFullCLM lam t hlam ht)) := by
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  let T : ℕ → SturmH lam →L[ℝ] SturmH lam :=
    sturmRealResolventFiniteRankTruncation lam t hlam
  have hbeta : Tendsto
      (fun N : ℕ => (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹)
      atTop (nhds 0) :=
    sturmResolventMultiplier_tendsto_zero lam t hlam ht
  change Tendsto T atTop (nhds R)
  refine Metric.tendsto_atTop.mpr ?_
  intro eps heps
  have hev : ∀ᶠ N : ℕ in atTop,
      (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ < eps :=
    hbeta.eventually (eventually_lt_nhds heps)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N₀, ?_⟩
  intro N hNN₀
  have hb := sturmRealClosedResolvent_finite_tail_norm_eq lam t hlam ht N
  have hscalar := hN₀ N hNN₀
  change ‖R - T N‖ = _ at hb
  rw [dist_eq_norm, norm_sub_rev, hb]
  exact hscalar

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_finite_tail_quadratic_rate
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_truncations_tendsto_opNorm

end GegenbauerFock.Ultraspherical
