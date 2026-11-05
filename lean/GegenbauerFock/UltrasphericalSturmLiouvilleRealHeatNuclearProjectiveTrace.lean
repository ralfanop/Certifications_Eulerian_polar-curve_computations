import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatTraceBasisSummable
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealS1EigenbasisToNuclear

/-!
# V007 — exact projective nuclear trace norm of the genuine real heat operator

For every lambda,s>0, the full, actually constructed Gegenbauer heat
operator on real weighted L2 has a complete orthonormal eigenbasis
with summable positive eigenvalues exp(-s*n*(n+2*lambda)).

The projective real Hilbert nuclear infimum is proved equal to their
sum, by an explicit positive rank-one representation for the upper
bound and the kernel-checked uniform finite-coordinate trace dual
inequality for the lower bound against *every* nuclear representation.

Unlike an explicit-witness mass equality, this is an exact universal
real nuclear infimum. It does not assert equivalence with the distinct
complex CFC/Physlib IsTraceClass API.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory InnerProductSpace Filter

private abbrev HeatH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine positive-time heat semigroup operator has a positive
summable diagonalization on the actual complete real Gegenbauer basis. -/
theorem sturmRealHeat_has_positive_real_spectralS1
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealPositiveS1Eigenbasis
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hpositive (n : ℕ) : 0 ≤ beta n :=
    (Real.exp_pos _).le
  have hsum : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have heig (n : ℕ) :
      sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) (b n) =
        beta n • b n := by
    have hb : b n = sturmMonicEigenCandidate_realL2_normalized
        lam hlam n := by
      simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
        HilbertBasis.coe_mkOfOrthogonalEqBot]
    rw [hb]
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
      lam hlam s (le_of_lt hs) n
  exact ⟨b, beta, hpositive, hsum, heig⟩

/-- Genuine real rank-one nuclear class membership for the actual
strictly positive-time heat operator, independently of a special
heat-series module. -/
theorem sturmRealHeat_has_real_nuclear_rank_one_series_viaS1
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealNuclearRankOneSeries
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) := by
  have hS1 : HasRealPositiveS1Eigenbasis
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) :=
    sturmRealHeat_has_positive_real_spectralS1 lam s hlam hs
  exact hS1.toPositiveRealNuclearExpansion.toRealNuclearRankOneSeries

/-- The universal real-Hilbert projective nuclear norm of the ACTUAL
heat operator is the exact spectral heat trace, not merely an upper
bound derived from the canonical rank-one representation. -/
theorem sturmRealHeat_realNuclearInfimum_eq_spectralTrace_directDuality
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    realNuclearInfimum
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
    ∑' n : ℕ, Real.exp
      (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  let T : HeatH lam →L[ℝ] HeatH lam :=
    sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hpositive (n : ℕ) : 0 ≤ beta n :=
    (Real.exp_pos _).le
  have hsum : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have heig (n : ℕ) : T (b n) = beta n • b n := by
    have hb : b n = sturmMonicEigenCandidate_realL2_normalized
        lam hlam n := by
      simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
        HilbertBasis.coe_mkOfOrthogonalEqBot]
    rw [hb]
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
      lam hlam s (le_of_lt hs) n
  have hseries : T = ∑' n : ℕ, beta n • rankOne ℝ (b n) (b n) :=
    realPositiveEigenSummable_operator_tsum_eq
      T b beta hpositive hsum heig
  have hterm (n : ℕ) :
      ‖beta n‖ * ‖b n‖ * ‖b n‖ = beta n := by
    rw [b.orthonormal.norm_eq_one n, Real.norm_eq_abs,
      abs_of_nonneg (hpositive n)]
    ring
  have hcost : Summable (fun n : ℕ =>
      ‖beta n‖ * ‖b n‖ * ‖b n‖) :=
    hsum.congr (fun n => (hterm n).symm)
  have hmem : (∑' n : ℕ, beta n) ∈ RealNuclearCosts T := by
    refine ⟨b, b, beta, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  have hupper : realNuclearInfimum T ≤ ∑' n : ℕ, beta n :=
    realNuclearInfimum_le_cost T hmem
  have hlower (c : ℝ) (hc : c ∈ RealNuclearCosts T) :
      (∑' n : ℕ, beta n) ≤ c := by
    have hfinite (N : ℕ) :
        (∑ n ∈ Finset.range N, beta n) ≤ c := by
      have hh := realHilbertFiniteTrace_abs_le_nuclearCost b N T hc
      have hd (n : ℕ) : inner ℝ (b n) (T (b n)) = beta n := by
        rw [heig n, real_inner_smul_right,
          real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
        ring
      have hfin :
          (∑ n ∈ Finset.range N, inner ℝ (b n) (T (b n))) =
            ∑ n ∈ Finset.range N, beta n :=
        Finset.sum_congr rfl (fun n _ => hd n)
      rw [hfin] at hh
      have hnonneg : 0 ≤ ∑ n ∈ Finset.range N, beta n :=
        Finset.sum_nonneg (fun n _ => hpositive n)
      simpa only [abs_of_nonneg hnonneg] using hh
    exact le_of_tendsto hsum.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)
  have hnonempty : (RealNuclearCosts T).Nonempty :=
    ⟨∑' n : ℕ, beta n, hmem⟩
  have hEq : realNuclearInfimum T = ∑' n : ℕ, beta n :=
    le_antisymm hupper (le_csInf hnonempty hlower)
  simpa only [T, beta] using hEq

/-- Joint positive spectral membership, general real nuclear
representation, and the exact optimal real nuclear trace norm. -/
theorem sturmRealHeat_positive_time_realS1_exact_certificate
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealPositiveS1Eigenbasis
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) ∧
    HasRealNuclearRankOneSeries
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) ∧
    realNuclearInfimum
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
      ∑' n : ℕ, Real.exp
        (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  exact ⟨sturmRealHeat_has_positive_real_spectralS1 lam s hlam hs,
    sturmRealHeat_has_real_nuclear_rank_one_series_viaS1 lam s hlam hs,
    sturmRealHeat_realNuclearInfimum_eq_spectralTrace_directDuality lam s hlam hs⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_has_positive_real_spectralS1
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_has_real_nuclear_rank_one_series_viaS1
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_realNuclearInfimum_eq_spectralTrace_directDuality
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_time_realS1_exact_certificate

end GegenbauerFock.Ultraspherical
