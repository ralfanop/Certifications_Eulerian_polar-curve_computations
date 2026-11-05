import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventTraceSeriesSummable
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — genuine positive real-Hilbert nuclear decomposition of the closed Sturm resolvent

The scalar summability certificate is upgraded to an equality of the
ACTUAL bounded operators on real ultraspherical weighted L²: the
resolvent equals the operator-norm convergent series of positive
orthogonal rank-one projections weighted by the exact eigenvalues.

The predicate below is an explicit positive nuclear decomposition
witness, not an alias for Physlib's *complex* CFC IsTraceClass.
Independence of this positive real trace from the chosen basis
and equivalence with a universal real Schatten S₁ ideal require
separate dedicated theorems.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace Filter

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Concrete positive real-Hilbert nuclear expansion: an orthonormal
family, a summable positive coefficient sequence, and equality with
the resulting operator-norm convergent rank-one series. -/
def HasRealPositiveNuclearExpansion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : Prop :=
  ∃ (e : ℕ → H) (β : ℕ → ℝ),
    Orthonormal ℝ e ∧ (∀ n, 0 ≤ β n) ∧ Summable β ∧
      A = ∑' n : ℕ, β n • rankOne ℝ (e n) (e n)

/-- The exact real Sturm positive rank-one series is absolutely
summable in ambient OPERATOR NORM. -/
theorem sturmRealResolvent_positive_nuclear_operator_summable
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let e : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hs : Summable β := sturmResolventMultiplier_summable lam t hlam ht
  have hn (n : ℕ) :
      ‖β n • rankOne ℝ (e n) (e n)‖ = β n := by
    rw [norm_smul, norm_rankOne,
      sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
    simp only [one_mul, mul_one, Real.norm_eq_abs]
    change |(t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹| =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
    exact abs_of_pos (sturmResolventMultiplier_pos lam t hlam ht n)
  apply Summable.of_norm
  convert hs using 1
  funext n
  exact hn n

/-- Operator-norm convergence of explicit positive spectral rank-one
series to the ACTUAL canonical-closure resolvent. -/
theorem sturmRealResolvent_positive_nuclear_operator_tsum_eq
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    sturmRealPositiveResolventFullCLM lam t hlam ht =
      ∑' n : ℕ,
        (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
          rankOne ℝ
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n) := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  let T : ℕ → SturmH lam →L[ℝ] SturmH lam :=
    sturmRealResolventFiniteRankTruncation lam t hlam
  have hdecay : Tendsto β atTop (nhds 0) :=
    sturmResolventMultiplier_tendsto_zero lam t hlam ht
  have hTend : Tendsto T atTop (nhds R) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro eps heps
    have hev : ∀ᶠ N : ℕ in atTop, β N < eps :=
      hdecay.eventually (eventually_lt_nhds heps)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    intro n hn
    have hnorm := sturmRealClosedResolvent_finite_tail_norm_eq lam t hlam ht n
    change ‖R - T n‖ = β n at hnorm
    rw [dist_eq_norm, norm_sub_rev, hnorm]
    exact hN n hn
  have hseries := sturmRealResolvent_positive_nuclear_operator_summable lam t hlam ht
  have hsumTend :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
              rankOne ℝ
                (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
                (sturmMonicEigenCandidate_realL2_normalized lam hlam n))
        atTop
        (nhds (∑' n : ℕ,
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
            rankOne ℝ
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n))) :=
    hseries.hasSum.tendsto_sum_nat
  have hTend' : Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
            rankOne ℝ
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      atTop (nhds R) := by
    change Tendsto T atTop (nhds R)
    exact hTend
  exact tendsto_nhds_unique hTend' hsumTend

/-- The actual closed real weighted-L² resolvent has a genuine
operator-norm summable, orthogonal positive rank-one nuclear witness. -/
theorem sturmRealResolvent_has_positive_real_nuclear_expansion
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    HasRealPositiveNuclearExpansion
      (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  let e : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  refine ⟨e, β, ?_, ?_, ?_, ?_⟩
  · exact sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam
  · intro n
    exact le_of_lt (sturmResolventMultiplier_pos lam t hlam ht n)
  · exact sturmResolventMultiplier_summable lam t hlam ht
  · exact sturmRealResolvent_positive_nuclear_operator_tsum_eq lam t hlam ht

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_positive_nuclear_operator_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_positive_nuclear_operator_tsum_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_has_positive_real_nuclear_expansion

end GegenbauerFock.Ultraspherical
