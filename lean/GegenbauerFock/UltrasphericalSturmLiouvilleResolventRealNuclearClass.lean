import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealPositiveNuclear
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearMass

/-!
# V007 — real Hilbert 1-nuclear operator characterization for the Sturm resolvent

A general rank-one series criterion for nuclear (S₁) operators on real
Hilbert spaces is provided here. Unlike the special positive diagonal
presentation, this predicate permits arbitrary left/right vectors and
signed real scalar coefficients.

The actual canonical closed Sturm resolvent satisfies this general
nuclear criterion, with the explicit positive Gegenbauer decomposition
constructed in the preceding modules.

This is a real-Hilbert nuclear-series realization of trace class.
We do NOT silently assert an equivalence, within the pinned Lean library,
to the separate *complex* CFC/Physlib trace-class predicate or its norm.
The exact mass proved in RealNuclearMass is the mass of the exhibited
positive series, not a postulated equality for arbitrary representations.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

/-- General real-Hilbert rank-one nuclear representation: summable
products of vector norms and scalar coefficients, with equality of
the resulting operator-norm sum to the actual bounded operator. -/
def HasRealNuclearRankOneSeries
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : Prop :=
  ∃ (u v : ℕ → H) (β : ℕ → ℝ),
    Summable (fun n : ℕ => ‖β n‖ * ‖u n‖ * ‖v n‖) ∧
      A = ∑' n : ℕ, β n • rankOne ℝ (u n) (v n)

/-- A nuclear-series witness automatically gives an absolutely
summable operator-norm rank-one decomposition, not merely a
formal scalar trace series. -/
theorem HasRealNuclearRankOneSeries.operator_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {A : H →L[ℝ] H}
    (hA : HasRealNuclearRankOneSeries A) :
    ∃ (u v : ℕ → H) (β : ℕ → ℝ),
      Summable (fun n : ℕ => β n • rankOne ℝ (u n) (v n)) ∧
        A = ∑' n : ℕ, β n • rankOne ℝ (u n) (v n) := by
  rcases hA with ⟨u, v, β, hs, hsum⟩
  refine ⟨u, v, β, ?_, hsum⟩
  apply Summable.of_norm
  convert hs using 1
  funext n
  rw [norm_smul, norm_rankOne]
  ring

/-- Every positive orthogonal nuclear expansion is, in particular,
a general (signed, two-vector) real-Hilbert rank-one nuclear series. -/
theorem HasRealPositiveNuclearExpansion.toRealNuclearRankOneSeries
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : H →L[ℝ] H}
    (hA : HasRealPositiveNuclearExpansion A) :
    HasRealNuclearRankOneSeries A := by
  rcases hA with ⟨e, β, he, hnonneg, hs, hsum⟩
  refine ⟨e, e, β, ?_, hsum⟩
  convert hs using 1
  funext n
  rw [he.norm_eq_one n, Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
  ring

/-- The ACTUAL real weighted-L² resolvent of the canonical closed
ultraspherical Sturm–Liouville operator is 1-nuclear, via a full
operator-norm convergent general rank-one series. -/
theorem sturmRealClosedResolvent_has_real_nuclear_rank_one_series
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    HasRealNuclearRankOneSeries
      (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  exact (sturmRealResolvent_has_positive_real_nuclear_expansion
    lam t hlam ht).toRealNuclearRankOneSeries

/-- The real-Hilbert 1-nuclear certification is accompanied by a
specific explicit positive representation whose rank-one norm mass
equals the finite scalar spectral trace of the actual resolvent. -/
theorem sturmRealClosedResolvent_nuclear_series_mass_certificate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    HasRealNuclearRankOneSeries
      (sturmRealPositiveResolventFullCLM lam t hlam ht) ∧
    (∑' n : ℕ,
      ‖(t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
      sturmResolventSpectralTrace lam t := by
  exact ⟨sturmRealClosedResolvent_has_real_nuclear_rank_one_series
    lam t hlam ht,
    sturmRealResolvent_positive_nuclear_mass_eq_trace lam t hlam ht⟩

#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.operator_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealPositiveNuclearExpansion.toRealNuclearRankOneSeries
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_has_real_nuclear_rank_one_series
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_nuclear_series_mass_certificate

end GegenbauerFock.Ultraspherical
