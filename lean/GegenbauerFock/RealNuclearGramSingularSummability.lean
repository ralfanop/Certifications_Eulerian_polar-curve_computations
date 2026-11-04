import GegenbauerFock.RealNuclearGramAdjointSingularRelation
import GegenbauerFock.RealNuclearGramNonzeroSingularTransfer
import GegenbauerFock.RealNuclearTwoOrthonormalAllCostsDual
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V007 — nuclearity forces summability of any actual singular amplitudes

This is the converse *summability* step for an arbitrary real-Hilbert
nuclear operator, conditional only on an actual orthonormal singular
family (not on an a priori summable family, a complete Hilbert basis,
a global unitary phase, or equal kernel/cokernel defects).

The existing sharp finite mixed-trace bound against EVERY admissible
nuclear representation gives uniformly bounded positive partial sums.
The real nonnegative-series criterion then gives summability.

This module does NOT construct the global spectral enumeration, CFC
absolute value, or polar partial isometry. They remain separate goals.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Any orthonormal source/target singular family has finite singular
mass at most EACH admissible real nuclear representation cost. -/
theorem realNuclearSingularFamily_finite_sum_le_cost
    (T : H →L[ℝ] H) (b c : ℕ → H)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ sigma n)
    (hpair : ∀ n, T (b n) = sigma n • c n)
    (N : ℕ) {cost : ℝ} (hcost : cost ∈ RealNuclearCosts T) :
    (∑ n ∈ Finset.range N, sigma n) ≤ cost := by
  have hdiag (n : ℕ) : inner ℝ (c n) (T (b n)) = sigma n := by
    rw [hpair n, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hc.norm_eq_one n]
    ring
  have htrace :=
    realTwoOrthonormalFiniteTrace_abs_le_nuclearCost
      b c hb hc N T hcost
  have hsum :
      (∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n))) =
        (∑ n ∈ Finset.range N, sigma n) :=
    Finset.sum_congr rfl (fun n _ => hdiag n)
  rw [hsum] at htrace
  have hp : 0 ≤ ∑ n ∈ Finset.range N, sigma n :=
    Finset.sum_nonneg (fun n _ => hnonneg n)
  simpa only [abs_of_nonneg hp] using htrace

/-- Nuclearity alone forces absolute summability of all nonnegative
amplitudes in any given orthonormal singular family, without
completeness or a unitary polar phase. -/
theorem HasRealNuclearRankOneSeries.singularFamily_summable
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ sigma n)
    (hpair : ∀ n, T (b n) = sigma n • c n) :
    Summable sigma := by
  rcases hT with ⟨u, v, beta, hs, hseries⟩
  have hcost :
      (∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖) ∈
        RealNuclearCosts T :=
    ⟨u, v, beta, hs, hseries, rfl⟩
  apply summable_of_sum_range_le hnonneg
  intro N
  exact realNuclearSingularFamily_finite_sum_le_cost
    T b c hb hc sigma hnonneg hpair N hcost

/-- The summed amplitudes of a supplied orthonormal singular family
are bounded by the INFIMUM over all real nuclear representations. -/
theorem HasRealNuclearRankOneSeries.singularFamily_tsum_le_infimum
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ sigma n)
    (hpair : ∀ n, T (b n) = sigma n • c n) :
    (∑' n : ℕ, sigma n) ≤ realNuclearInfimum T := by
  have hs : Summable sigma :=
    hT.singularFamily_summable b c hb hc sigma hnonneg hpair
  obtain ⟨u, v, beta, hcostsum, hseries⟩ := hT
  have hnonempty : (RealNuclearCosts T).Nonempty :=
    ⟨∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖,
      ⟨u, v, beta, hcostsum, hseries, rfl⟩⟩
  change (∑' n : ℕ, sigma n) ≤ sInf (RealNuclearCosts T)
  apply le_csInf hnonempty
  intro cost hcost
  exact hs.tsum_le_of_sum_range_le
    (fun N => realNuclearSingularFamily_finite_sum_le_cost
      T b c hb hc sigma hnonneg hpair N hcost)

/-- Apply the converse summability theorem to the ACTUAL nuclear
Gram eigenmodes with positive singular amplitudes. The normalized
output singular family is constructed from T itself. -/
theorem HasRealNuclearRankOneSeries.gram_nonzero_singular_summable
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : ℕ → H) (hb : Orthonormal ℝ b)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 < sigma n)
    (heig : ∀ n, realNuclearGram T (b n) =
      (sigma n)^2 • b n) :
    Summable sigma := by
  let c : ℕ → H := fun n => (sigma n)⁻¹ • T (b n)
  have hc : Orthonormal ℝ c :=
    realNuclearGram_nonzero_output_orthonormal
      T b hb sigma hpos heig
  have hpair : ∀ n, T (b n) = sigma n • c n :=
    realNuclearGram_nonzero_source_output_relation T b sigma hpos
  exact hT.singularFamily_summable
    b c hb hc sigma (fun n => (hpos n).le) hpair

/-- Universal nuclear-infimum bound for ANY positive Gram eigenfamily
of the actual nonselfadjoint real operator, not a diagonal surrogate. -/
theorem HasRealNuclearRankOneSeries.gram_nonzero_singular_tsum_le_infimum
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b : ℕ → H) (hb : Orthonormal ℝ b)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 < sigma n)
    (heig : ∀ n, realNuclearGram T (b n) =
      (sigma n)^2 • b n) :
    (∑' n : ℕ, sigma n) ≤ realNuclearInfimum T := by
  let c : ℕ → H := fun n => (sigma n)⁻¹ • T (b n)
  have hc : Orthonormal ℝ c :=
    realNuclearGram_nonzero_output_orthonormal
      T b hb sigma hpos heig
  have hpair : ∀ n, T (b n) = sigma n • c n :=
    realNuclearGram_nonzero_source_output_relation T b sigma hpos
  exact hT.singularFamily_tsum_le_infimum
    b c hb hc sigma (fun n => (hpos n).le) hpair

#print axioms GegenbauerFock.Ultraspherical.realNuclearSingularFamily_finite_sum_le_cost
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.singularFamily_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.singularFamily_tsum_le_infimum
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_nonzero_singular_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_nonzero_singular_tsum_le_infimum

end GegenbauerFock.Ultraspherical
