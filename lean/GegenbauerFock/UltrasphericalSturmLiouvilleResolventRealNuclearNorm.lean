import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearClass
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# V007 — real Hilbert nuclear projective cost and its optimal infimum

For any complete real Hilbert space we define the collection of costs
of ALL absolutely summable real rank-one series representing a given
bounded operator. Their infimum is the real-Hilbert 1-nuclear norm
candidate. This does NOT identify it with an unrelated complex
CFC trace-class norm.

The present module proves the genuine resolvent has an admissible
representation of exact spectral-trace cost, hence the universal
nuclear infimum is bounded above by that trace. The reverse inequality
(duality against spectral cutoffs) is a separate theorem and MUST NOT
be inferred from the positivity of this one representation.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- All costs of arbitrary admissible absolutely summable real-Hilbert
rank-one representations of an actual bounded operator. -/
def RealNuclearCosts (T : H →L[ℝ] H) : Set ℝ :=
  {c | ∃ (u v : ℕ → H) (β : ℕ → ℝ),
    Summable (fun n : ℕ => ‖β n‖ * ‖u n‖ * ‖v n‖) ∧
    T = ∑' n : ℕ, β n • rankOne ℝ (u n) (v n) ∧
    c = ∑' n : ℕ, ‖β n‖ * ‖u n‖ * ‖v n‖}

/-- Every admissible representation cost is nonnegative. -/
theorem RealNuclearCosts.nonneg (T : H →L[ℝ] H)
    {c : ℝ} (hc : c ∈ RealNuclearCosts T) : 0 ≤ c := by
  obtain ⟨u, v, β, _, _, rfl⟩ := hc
  exact tsum_nonneg (fun n => by positivity)

/-- The set of nuclear costs has the uniform lower bound zero. -/
theorem RealNuclearCosts.bddBelow (T : H →L[ℝ] H) :
    BddBelow (RealNuclearCosts T) := by
  refine ⟨0, ?_⟩
  intro c hc
  exact RealNuclearCosts.nonneg T hc

/-- Projective nuclear cost infimum (the real Hilbert S₁ norm candidate).
For a non-nuclear operator the cost set is empty; the mathematical
trace norm is used only together with a nuclear-series witness. -/
noncomputable def realNuclearInfimum (T : H →L[ℝ] H) : ℝ :=
  sInf (RealNuclearCosts T)

/-- Every concrete admissible nuclear representation provides an
upper bound on the universal infimum over ALL such representations. -/
theorem realNuclearInfimum_le_cost (T : H →L[ℝ] H)
    {c : ℝ} (hc : c ∈ RealNuclearCosts T) :
    realNuclearInfimum T ≤ c := by
  unfold realNuclearInfimum
  exact csInf_le (RealNuclearCosts.bddBelow T) hc

/-- The genuine real Sturm resolvent's universal nuclear infimum is
bounded ABOVE by its certified spectral trace. This is not yet the
reverse inequality or equality of the two quantities. -/
theorem sturmRealClosedResolvent_nuclearInfimum_le_spectralTrace
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) ≤
      sturmResolventSpectralTrace lam t := by
  let e : ℕ → Lp ℝ 2 (measure lam) :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hterm (n : ℕ) :
      ‖β n‖ * ‖e n‖ * ‖e n‖ = β n := by
    rw [sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n,
      Real.norm_eq_abs, abs_of_pos
        (sturmResolventMultiplier_pos lam t hlam ht n)]
    ring
  have hcost : Summable (fun n : ℕ =>
      ‖β n‖ * ‖e n‖ * ‖e n‖) :=
    (sturmResolventMultiplier_summable lam t hlam ht).congr
      (fun n => (hterm n).symm)
  have hseries :
      sturmRealPositiveResolventFullCLM lam t hlam ht =
        ∑' n : ℕ, β n • rankOne ℝ (e n) (e n) :=
    sturmRealResolvent_positive_nuclear_operator_tsum_eq lam t hlam ht
  have hmem :
      (∑' n : ℕ, ‖β n‖ * ‖e n‖ * ‖e n‖) ∈
        RealNuclearCosts
          (sturmRealPositiveResolventFullCLM lam t hlam ht) :=
    ⟨e, e, β, hcost, hseries, rfl⟩
  calc
    realNuclearInfimum (sturmRealPositiveResolventFullCLM lam t hlam ht) ≤
        ∑' n : ℕ, ‖β n‖ * ‖e n‖ * ‖e n‖ :=
      realNuclearInfimum_le_cost _ hmem
    _ = sturmResolventSpectralTrace lam t := by
      unfold sturmResolventSpectralTrace
      exact tsum_congr hterm

#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.nonneg
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.bddBelow
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_le_cost
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_nuclearInfimum_le_spectralTrace

end GegenbauerFock.Ultraspherical
