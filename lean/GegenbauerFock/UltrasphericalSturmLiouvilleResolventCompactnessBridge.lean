import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteRankTruncations
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — compactness bridge for the genuine closed Sturm resolvent

The actual positive-shift closed Sturm resolvent is compact as soon as
its difference from the explicitly constructed finite-rank spectral
truncations satisfies the expected uniform spectral-tail estimate.

This theorem does NOT assert the tail estimate as an assumption-free
fact. Its explicit hypothesis identifies the sole missing quantitative
operator-norm step, distinct from scalar multiplier convergence or
strong L² convergence.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A precise bridge from the expected uniform spectral-tail bound
to actual compactness of the canonical closed real Sturm resolvent. -/
theorem sturmRealClosedResolvent_compact_of_uniform_tail_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hbound : ∀ N : ℕ,
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ ≤
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹) :
    IsCompactOperator (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  let T : ℕ → SturmH lam →L[ℝ] SturmH lam :=
    sturmRealResolventFiniteRankTruncation lam t hlam
  have hbeta :
      Tendsto (fun N : ℕ =>
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹)
        atTop (nhds 0) :=
    sturmResolventMultiplier_tendsto_zero lam t hlam ht
  have hlimit : Tendsto T atTop (nhds R) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro eps heps
    have hev : ∀ᶠ N : ℕ in atTop,
        (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ < eps :=
      hbeta.eventually (eventually_lt_nhds heps)
    filter_upwards [hev] with N hN
    have hb := hbound N
    change ‖R - T N‖ ≤ _ at hb
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt hb hN
  have hcompact : ∀ N : ℕ, IsCompactOperator (T N) := by
    intro N
    exact sturmRealResolventFiniteRankTruncation_compact lam t hlam N
  exact isCompactOperator_of_tendsto hlimit (Eventually.of_forall hcompact)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_compact_of_uniform_tail_bound

end GegenbauerFock.Ultraspherical
